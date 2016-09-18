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
use syntax::parse::{ParseSess};
use syntax::parse::token::{Token};
use syntax::tokenstream::{TokenTree};

use super::extractor;
use super::{PluginResult};
use super::specification::{Amount, Sequence, Specifier, Variant};
use super::utility::{self, TransactionParser};

//================================================
// Structs
//================================================

// Arguments _____________________________________

/// A set of parsed arguments.
#[derive(Debug)]
pub struct Arguments(HashMap<String, Box<Any>>);

impl Arguments {
    //- Accessors --------------------------------

    /// Returns the argument with the suppled name.
    pub fn get<T: Any + Clone>(&self, name: &str) -> T {
        get(self.0.get(name).unwrap())
    }

    /// Returns the sequence arguments with the supplied name.
    pub fn get_sequence(&self, name: &str) -> SequenceArguments {
        get_sequence(self.0.get(name).unwrap())
    }

    /// Returns the enum arguments with the supplied name.
    pub fn get_enum(&self, name: &str) -> EnumArguments {
        get_enum(self.0.get(name).unwrap())
    }
}

// SequenceArguments _____________________________

/// A set of parsed arguments found in a sequence.
#[derive(Debug)]
pub struct SequenceArguments<'a>(Vec<&'a Box<Any>>);

impl<'a> SequenceArguments<'a> {
    //- Consumers -------------------------------

    /// Returns the arguments as an `Option`.
    pub fn into_option<T: Any + Clone>(self) -> Option<T> {
        self.0.into_iter().next().map(get)
    }

    /// Returns the arguments as a `Vec`.
    pub fn into_vec<T: Any + Clone>(self) -> Vec<T> {
        self.0.into_iter().map(get).collect()
    }

    /// Returns the arguments as an `Option`.
    pub fn into_enum_option<T, F: Fn(EnumArguments<'a>) -> T>(self, f: F) -> Option<T> {
        self.0.into_iter().next().map(get_enum).map(f)
    }

    /// Returns the arguments as a `Vec`.
    pub fn into_enum_vec<T, F: Fn(EnumArguments<'a>) -> T>(self, f: F) -> Vec<T> {
        self.0.into_iter().map(get_enum).map(f).collect()
    }

    /// Returns the arguments as sequences.
    pub fn into_sequence_option<T, F: Fn(SequenceArguments<'a>) -> T>(self, f: F) -> Option<T> {
        self.0.into_iter().next().map(get_sequence).map(f)
    }

    /// Returns the arguments as sequences.
    pub fn into_sequence_vec<T, F: Fn(SequenceArguments<'a>) -> T>(self, f: F) -> Vec<T> {
        self.0.into_iter().map(get_sequence).map(f).collect()
    }
}

// EnumArguments _________________________________

/// A set of parsed arguments found in an enum.
#[derive(Debug)]
pub struct EnumArguments<'a> {
    /// The variant index of these arguments.
    pub variant: usize,
    /// The arguments.
    pub arguments: &'a Arguments,
}

//================================================
// Functions
//================================================

fn get<T: Any + Clone>(any: &Box<Any>) -> T {
    any.downcast_ref::<T>().unwrap().clone()
}

#[cfg_attr(feature="clippy", allow(needless_lifetimes))]
fn get_sequence<'a>(any: &'a Box<Any>) -> SequenceArguments<'a> {
    SequenceArguments(any.downcast_ref::<Vec<Box<Any>>>().unwrap().iter().collect())
}

#[cfg_attr(feature="clippy", allow(needless_lifetimes))]
fn get_enum<'a>(any: &'a Box<Any>) -> EnumArguments<'a> {
    let &(variant, ref arguments) = any.downcast_ref::<(usize, Arguments)>().unwrap();
    EnumArguments { variant: variant, arguments: arguments }
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
fn expect_specific_token(parser: &mut TransactionParser, expected: &Token) -> PluginResult<()> {
    let description = format!("`{}`", pprust::token_to_string(expected));
    let (span, found) = try!(parser.next_token(&description, None));
    if mtwt_eq(&found, expected) {
        Ok(())
    } else {
        Err((span, format!("expected {}", description)))
    }
}

/// Parses sequence arguments.
fn parse_sequence(
    parser: &mut TransactionParser,
    sequence: &Sequence,
    arguments: &mut Arguments,
) -> PluginResult<usize> {
    if sequence.specification.is_empty() {
        return Ok(0);
    }
    // Insert empty sequence matches for each named specifier in the sequence.
    for specifier in &sequence.specification {
        if let Some(name) = specifier.get_name() {
            arguments.0.insert(name.clone(), Box::new(Vec::<Box<Any>>::new()));
        }
    }
    let mut count = 0;
    loop {
        parser.save();
        // Check for a separator if expected.
        if let Some(ref separator) = sequence.separator {
            if count != 0 && !parser.eat(separator) {
                return Ok(count);
            }
        }
        // Attempt to parse an occurrence of the sequence.
        let mut subarguments = Arguments(HashMap::new());
        match parse_arguments_impl(parser, &sequence.specification, &mut subarguments) {
            Ok(()) => count += 1,
            Err(error) => if count == 0 && sequence.amount == Amount::OneOrMore {
                return Err(error);
            } else {
                parser.rollback();
                return Ok(count);
            },
        }
        // Append the occurrence arguments to the parent arguments.
        for (k, v) in subarguments.0 {
            let argument = arguments.0.entry(k).or_insert_with(|| Box::new(Vec::<Box<Any>>::new()));
            argument.downcast_mut::<Vec<Box<Any>>>().unwrap().push(v);
        }
        // Return if this sequence doesn't expect multiple occurrences.
        if sequence.amount == Amount::ZeroOrOne {
            return Ok(count);
        }
    }
}

/// Parses enumerated arguments.
fn parse_enum(
    parser: &mut TransactionParser,
    variants: &[Variant],
) -> PluginResult<Box<Any>> {
    for (index, variant) in variants.iter().enumerate() {
        parser.save();
        let mut subarguments = Arguments(HashMap::new());
        match parse_arguments_impl(parser, &variant.specification, &mut subarguments) {
            Ok(()) => return Ok(Box::new((index, subarguments))),
            Err(error) => if index + 1 == variants.len() {
                return Err(error);
            },
        }
    }
    unreachable!()
}

/// Actually parses the supplied arguments with the supplied argument specification.
fn parse_arguments_impl(
    parser: &mut TransactionParser,
    specification: &[Specifier],
    arguments: &mut Arguments,
) -> PluginResult<()> {
    macro_rules! insert {
        ($parse:ident$(.$field:ident)*, $name:expr) => ({
            let (_, argument) = try!(parser.$parse($name));
            arguments.0.insert($name.clone(), Box::new(argument$(.$field)*));
        });

        (SPANNED: $parse:ident$(.$field:ident)*, $name:expr) => ({
            let (span, argument) = try!(parser.$parse($name));
            let spanned = codemap::respan(span, argument$(.$field)*);
            arguments.0.insert($name.clone(), Box::new(spanned));
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
                try!(parse_arguments_impl(parser, &[(*extractor.specifier).clone()], arguments));
                let extractor = &extractor.extractor;
                let argument = extractor::extract(extractor, &*arguments.0.get(name).unwrap());
                arguments.0.insert(name.clone(), try!(argument));
            },
            Specifier::Specific(ref token) => try!(expect_specific_token(parser, token)),
            Specifier::Delimited(ref delimited) => {
                try!(expect_specific_token(parser, &Token::OpenDelim(delimited.delimiter)));
                try!(parse_arguments_impl(parser, &delimited.specification, arguments));
                try!(expect_specific_token(parser, &Token::CloseDelim(delimited.delimiter)));
            },
            Specifier::Sequence(ref name, ref sequence) => {
                let start = parser.get_span();
                let count = try!(parse_sequence(parser, sequence, arguments));
                if let Some(ref name) = *name {
                    let span = utility::span_spans(start, parser.get_last_span());
                    if sequence.amount == Amount::ZeroOrOne {
                        let found = count != 0;
                        arguments.0.insert(name.clone(), Box::new(codemap::respan(span, found)));
                    } else {
                        arguments.0.insert(name.clone(), Box::new(codemap::respan(span, count)));
                    }
                }
            },
            Specifier::Enum(ref name, ref variants) => {
                arguments.0.insert(name.clone(), try!(parse_enum(parser, variants)));
            },
        }
    }
    Ok(())
}

/// Parses the supplied arguments with the supplied argument specification.
pub fn parse_arguments(
    session: &ParseSess, tts: &[TokenTree], specification: &[Specifier]
) -> PluginResult<Arguments> {
    if tts.is_empty() && specification.is_empty() {
        return Ok(Arguments(HashMap::new()));
    }
    let mut parser = TransactionParser::new(session, tts);
    let mut arguments = Arguments(HashMap::new());
    try!(parse_arguments_impl(&mut parser, specification, &mut arguments));
    if let Some(remainder) = parser.get_remainder_span() {
        Err((remainder, "too many arguments".into()))
    } else {
        Ok(arguments)
    }
}
