// Copyright 2016 Kyle Mayes
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Arguments.

use std::any::{Any};
use std::collections::{HashMap};

use syntax::codemap;
use syntax::print::pprust;
use syntax::ext::base::{ExtCtxt};
use syntax::parse::token::{Token};
use syntax::tokenstream::{TokenTree};

use super::extractor;
use super::{PluginResult};
use super::specification::{Amount, Enum, Sequence, Specification, Specifier, Struct};
use super::utility::{self, TransactionParser};

//================================================
// Macros
//================================================

// downcast_ref! _________________________________

macro_rules! downcast_ref {
    ($ty:ty, $argument:expr, $name:expr) => ({
        match $argument.downcast_ref::<$ty>() {
            Some(argument) => argument,
            _ => panic!("invalid argument type: '{}'", $name),
        }
    });

    ($argument:expr, $name:expr) => (downcast_ref!(T, $argument, $name));
}

//================================================
// Structs
//================================================

// Arguments _____________________________________

/// A set of parsed arguments.
#[derive(Debug)]
pub struct Arguments {
    /// The variant index of this set of parsed arguments, if any.
    pub variant: Option<usize>,
    /// The parsed arguments.
    pub arguments: HashMap<String, Box<Any>>,
}

impl Arguments {
    //- Constructors -----------------------------

    fn new() -> Arguments {
        Arguments { variant: None, arguments: HashMap::new() }
    }

    //- Mutators ---------------------------------

    fn insert<T: Any>(&mut self, name: String, value: T) {
        self.arguments.insert(name, Box::new(value));
    }

    //- Accessors --------------------------------

    fn get_ref<T: Any>(&self, name: &str) -> &T {
        match self.arguments.get(name) {
            Some(argument) => downcast_ref!(argument, name),
            _ => panic!("no such argument: '{}'", name),
        }
    }

    /// Returns the argument with the suppled name.
    pub fn get<T: Any + Clone>(&self, name: &str) -> T {
        self.get_ref::<T>(name).clone()
    }

    /// Returns the enumerated or structured arguments with the supplied name.
    pub fn get_arguments(&self, name: &str) -> &Arguments {
        self.get_ref::<Arguments>(name)
    }

    /// Returns the sequence arguments with the supplied name.
    pub fn get_sequence(&self, name: &str) -> SequenceArguments {
        let arguments = if self.arguments.contains_key(name) {
            self.get_ref::<Vec<Box<Any>>>(name).iter().collect()
        } else {
            vec![]
        };
        SequenceArguments::new(name, arguments)
    }
}

// SequenceArguments _____________________________

/// A set of parsed arguments found in a sequence.
#[derive(Debug)]
pub struct SequenceArguments<'a> {
    name: String,
    arguments: Vec<&'a Box<Any>>,
}

impl<'a> SequenceArguments<'a> {
    //- Constructors -----------------------------

    fn new(name: &str, arguments: Vec<&'a Box<Any>>) -> SequenceArguments<'a> {
        SequenceArguments { name: name.into(), arguments: arguments }
    }

    //- Accessors --------------------------------

    /// Returns the arguments as an `Option`.
    pub fn to_option<T: Any + Clone>(&self) -> Option<T> {
        self.arguments.iter().next().map(|a| downcast_ref!(a, &self.name).clone())
    }

    /// Returns the arguments as a `Vec`.
    pub fn to_vec<T: Any + Clone>(&self) -> Vec<T> {
        self.arguments.iter().map(|a| downcast_ref!(a, &self.name).clone()).collect()
    }

    /// Returns the arguments as an `Option`.
    pub fn to_arguments_option<T, F: Fn(&'a Arguments) -> T>(&self, f: F) -> Option<T> {
        self.arguments.iter().next().map(|a| f(downcast_ref!(Arguments, a, &self.name)))
    }

    /// Returns the arguments as a `Vec`.
    pub fn to_arguments_vec<T, F: Fn(&'a Arguments) -> T>(&self, f: F) -> Vec<T> {
        self.arguments.iter().map(|a| f(downcast_ref!(Arguments, a, &self.name))).collect()
    }

    /// Returns the arguments as sequences.
    pub fn to_sequence_option<T, F: Fn(SequenceArguments<'a>) -> T>(&self, f: F) -> Option<T> {
        self.arguments.iter().next().map(|a| {
            let arguments = downcast_ref!(Vec<Box<Any>>, a, &self.name);
            f(SequenceArguments::new(&self.name, arguments.iter().collect()))
        })
    }

    /// Returns the arguments as sequences.
    pub fn to_sequence_vec<T, F: Fn(SequenceArguments<'a>) -> T>(&self, f: F) -> Vec<T> {
        self.arguments.iter().map(|a| {
            let arguments = downcast_ref!(Vec<Box<Any>>, a, &self.name);
            f(SequenceArguments::new(&self.name, arguments.iter().collect()))
        }).collect()
    }
}

//================================================
// Functions
//================================================

#[allow(dead_code)]
struct State<'a, 'b: 'a> {
    context: &'a ExtCtxt<'b>,
    parser: TransactionParser,
}

/// Returns whether the supplied tokens are equal.
fn mtwt_eq(left: &Token, right: &Token) -> bool {
    match (left, right) {
        (&Token::Ident(left), &Token::Ident(right)) |
        (&Token::Lifetime(left), &Token::Lifetime(right)) =>
            left.name.as_str() == right.name.as_str(),
        _ => left == right,
    }
}

/// Returns `Ok` if the supplied token is next in the supplied parser.
fn expect_specific_token(state: &mut State, expected: &Token) -> PluginResult<()> {
    let description = format!("`{}`", pprust::token_to_string(expected));
    let (span, found) = try!(state.parser.next_token(&description, None));
    if mtwt_eq(&found, expected) {
        Ok(())
    } else {
        Err((span, format!("expected {}", description)))
    }
}

/// Parses sequence arguments.
fn parse_sequence(
    state: &mut State, sequence: &Sequence, arguments: &mut Arguments
) -> PluginResult<usize> {
    if sequence.specification.is_empty() {
        return Ok(0);
    }
    // Insert empty sequence matches for each named specifier in the sequence.
    for specifier in &sequence.specification {
        if let Some(name) = specifier.get_name() {
            arguments.insert(name.clone(), Vec::<Box<Any>>::new());
        }
    }
    let mut count = 0;
    loop {
        let transaction = state.parser.transaction();
        // Check for a separator if expected.
        if let Some(ref separator) = sequence.separator {
            if count != 0 && !state.parser.eat(separator) {
                return Ok(count);
            }
        }
        // Attempt to parse an occurrence of the sequence.
        let mut subarguments = Arguments::new();
        match parse_arguments_impl(state, &sequence.specification, &mut subarguments) {
            Ok(()) => count += 1,
            Err(error) => if count == 0 && sequence.amount == Amount::OneOrMore {
                return Err(error);
            } else {
                transaction.rollback(&mut state.parser);
                return Ok(count);
            },
        }
        // Append the occurrence arguments to the parent arguments.
        for (k, v) in subarguments.arguments {
            let argument = arguments.arguments.entry(k).or_insert_with(|| {
                Box::new(Vec::<Box<Any>>::new())
            });
            argument.downcast_mut::<Vec<Box<Any>>>().unwrap().push(v);
        }
        // Return if this sequence doesn't expect multiple occurrences.
        if sequence.amount == Amount::ZeroOrOne {
            return Ok(count);
        }
    }
}

/// Parses enumerated arguments.
fn parse_enum(state: &mut State, enum_: &Enum) -> PluginResult<Arguments> {
    for (index, variant) in enum_.variants.iter().enumerate() {
        let transaction = state.parser.transaction();
        let mut subarguments = Arguments::new();
        subarguments.variant = Some(index);
        if variant.specification.is_empty() {
            return Ok(subarguments);
        }
        match parse_arguments_impl(state, &variant.specification, &mut subarguments) {
            Ok(()) => return Ok(subarguments),
            _ => transaction.rollback(&mut state.parser),
        }
    }
    Err((state.parser.get_span(), format!("expected 'enum {}'", enum_.name)))
}

/// Parses structured arguments.
fn parse_struct(state: &mut State, struct_: &Struct) -> PluginResult<Arguments> {
    let mut arguments = Arguments::new();
    try!(parse_arguments_impl(state, &struct_.specification, &mut arguments));
    Ok(arguments)
}

/// Actually parses the supplied arguments with the supplied argument specification.
fn parse_arguments_impl(
    state: &mut State,
    specification: &[Specifier],
    arguments: &mut Arguments,
) -> PluginResult<()> {
    macro_rules! insert {
        ($parse:ident$(.$field:ident)*, $name:expr) => ({
            let (_, argument) = try!(state.parser.$parse($name));
            arguments.insert($name.clone(), argument$(.$field)*);
        });

        (SPANNED: $parse:ident$(.$field:ident)*, $name:expr) => ({
            let (span, argument) = try!(state.parser.$parse($name));
            let spanned = codemap::respan(span, argument$(.$field)*);
            arguments.insert($name.clone(), spanned);
        });
    }

    for specifier in specification {
        match *specifier {
            Specifier::Attr(ref name) => insert!(parse_attribute, name),
            Specifier::BinOp(ref name) => insert!(SPANNED: parse_binop, name),
            Specifier::Block(ref name) => insert!(parse_block, name),
            Specifier::Delim(ref name) => insert!(SPANNED: parse_delim, name),
            Specifier::Expr(ref name) => insert!(parse_expr, name),
            Specifier::Ident(ref name) => insert!(SPANNED: parse_ident, name),
            Specifier::Item(ref name) => insert!(parse_item, name),
            Specifier::Lftm(ref name) => insert!(SPANNED: parse_lifetime.name, name),
            Specifier::Lit(ref name) => insert!(parse_lit, name),
            Specifier::Meta(ref name) => insert!(parse_meta_item, name),
            Specifier::Pat(ref name) => insert!(parse_pat, name),
            Specifier::Path(ref name) => insert!(parse_path, name),
            Specifier::Stmt(ref name) => insert!(parse_stmt, name),
            Specifier::Ty(ref name) => insert!(parse_ty, name),
            Specifier::Tok(ref name) => insert!(SPANNED: parse_token, name),
            Specifier::Tt(ref name) => insert!(parse_token_tree, name),
            Specifier::Extractor(ref name, ref extractor) => {
                try!(parse_arguments_impl(state, &[(*extractor.specifier).clone()], arguments));
                let extractor = &extractor.extractor;
                let argument = extractor::extract(extractor, &*arguments.arguments.get(name).unwrap());
                arguments.arguments.insert(name.clone(), try!(argument));
            },
            Specifier::Specific(ref token) => try!(expect_specific_token(state, token)),
            Specifier::Delimited(ref delimited) => {
                try!(expect_specific_token(state, &Token::OpenDelim(delimited.delimiter)));
                try!(parse_arguments_impl(state, &delimited.specification, arguments));
                try!(expect_specific_token(state, &Token::CloseDelim(delimited.delimiter)));
            },
            Specifier::Sequence(ref name, ref sequence) => {
                let start = state.parser.get_span();
                let count = try!(parse_sequence(state, sequence, arguments));
                if let Some(ref name) = *name {
                    let span = utility::span_spans(start, state.parser.get_last_span());
                    if sequence.amount == Amount::ZeroOrOne {
                        let found = count != 0;
                        arguments.insert(name.clone(), codemap::respan(span, found));
                    } else {
                        arguments.insert(name.clone(), codemap::respan(span, count));
                    }
                }
            },
            Specifier::Enum(ref name, ref enum_) => {
                arguments.insert(name.clone(), try!(parse_enum(state, enum_)));
            },
            Specifier::Struct(ref name, ref struct_) => {
                arguments.insert(name.clone(), try!(parse_struct(state, struct_)));
            },
        }
    }
    Ok(())
}

/// Parses the supplied arguments with the supplied enumerated argument specification.
fn parse_arguments_enum(
    context: &ExtCtxt, tts: &[TokenTree], enum_: &Enum
) -> PluginResult<Arguments> {
    if tts.is_empty() {
        for (index, variant) in enum_.variants.iter().enumerate() {
            if variant.specification.is_empty() {
                let mut arguments = Arguments::new();
                arguments.variant = Some(index);
                return Ok(arguments);
            }
        }
    }
    let parser = TransactionParser::new(context.parse_sess, tts);
    let mut state = State { context: context, parser: parser };
    let arguments = try!(parse_enum(&mut state, enum_));
    if let Some(remainder) = state.parser.get_remainder_span() {
        Err((remainder, "too many arguments".into()))
    } else {
        Ok(arguments)
    }
}

/// Parses the supplied arguments with the supplied structured argument specification.
fn parse_arguments_struct(
    context: &ExtCtxt, tts: &[TokenTree], struct_: &Struct
) -> PluginResult<Arguments> {
    if tts.is_empty() && struct_.specification.is_empty() {
        return Ok(Arguments::new());
    }
    let parser = TransactionParser::new(context.parse_sess, tts);
    let mut state = State { context: context, parser: parser };
    let arguments = try!(parse_struct(&mut state, struct_));
    if let Some(remainder) = state.parser.get_remainder_span() {
        Err((remainder, "too many arguments".into()))
    } else {
        Ok(arguments)
    }
}

/// Parses the supplied arguments with the supplied argument specification.
pub fn parse_arguments(
    context: &ExtCtxt, tts: &[TokenTree], specification: &Specification
) -> PluginResult<Arguments> {
    match *specification {
        Specification::Enum(ref enum_) => parse_arguments_enum(context, tts, enum_),
        Specification::Struct(ref struct_) => parse_arguments_struct(context, tts, struct_),
    }
}
