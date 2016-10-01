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

//! Argument specifications.

use std::collections::{HashMap, HashSet};

use syntax::ast::{Ident};
use syntax::codemap::{Span, DUMMY_SP};
use syntax::ext::base::{ExtCtxt};
use syntax::parse::{self, ParseSess};
use syntax::parse::token::{self, BinOpToken, DelimToken, Token};
use syntax::tokenstream::{TokenTree};

use super::extractor;
use super::utility::{self, PluginResult};

//================================================
// Macros
//================================================

// expect_tt! ____________________________________

/// Attempts to get the next token tree in the supplied iterator, returning early if unsuccessful.
macro_rules! expect_tt {
    (DELIMITED: $span:expr, $tts:expr) => ({
        match expect_tt!($span, $tts) {
            &TokenTree::Delimited(_, ref delimited) => &delimited.tts,
            tt => return Err((tt.span(), "expected delimited".into())),
        }
    });

    (IDENTIFIER: $span:expr, $tts:expr) => ({
        match expect_tt!($span, $tts) {
            &TokenTree::Token(_, Token::Ident(ident)) => ident.name.as_str().to_string(),
            tt => return Err((tt.span(), "expected identifier".into())),
        }
    });

    ($span:expr, $tts:expr) => ({
        try!($tts.next().ok_or_else(|| ($span, "unexpected end of specification".into())))
    });
}

//================================================
// Enums
//================================================

// Amount ________________________________________

/// Indicates how many times a sequence is expected to occur.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Amount {
    /// `+`
    OneOrMore,
    /// `*`
    ZeroOrMore,
    /// `?`
    ZeroOrOne,
}

// Specification _________________________________

/// An argument specification.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Specification {
    /// An enumerated argument specification.
    Enum(Enum),
    /// A structured argument specification.
    Struct(Struct),
}

// Specifier _____________________________________

/// A piece of a argument specification.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Specifier {
    /// An attribute.
    Attr(String),
    /// A binary operator.
    BinOp(String),
    /// A brace-delimited sequence of statements.
    Block(String),
    /// A delimited sequence of token trees.
    Delim(String),
    /// An expression.
    Expr(String),
    /// An identifier.
    Ident(String),
    /// An item.
    Item(String),
    /// A lifetime.
    Lftm(String),
    /// A literal.
    Lit(String),
    /// A "meta" item, as found in attributes.
    Meta(String),
    /// A pattern.
    Pat(String),
    /// A qualified name.
    Path(String),
    /// A single statement.
    Stmt(String),
    /// A type.
    Ty(String),
    /// A single token.
    Tok(String),
    /// A single token tree.
    Tt(String),
    /// A piece that will be filtered through an extraction function.
    Extractor(String, Extractor),
    /// A non-variable piece.
    Specific(Token),
    /// A delimited piece.
    Delimited(Delimited),
    /// A sequence piece which may be named.
    Sequence(Option<String>, Sequence),
    /// An enumerated piece.
    Enum(String, Enum),
    /// A structured piece.
    Struct(String, Struct),
}

impl Specifier {
    //- Constructors -----------------------------

    /// Constructs a specifier for a simple named specifier.
    fn simple(name: String, specifier: &str) -> Option<Specifier> {
        match specifier {
            "attr" => Some(Specifier::Attr(name)),
            "binop" => Some(Specifier::BinOp(name)),
            "block" => Some(Specifier::Block(name)),
            "delim" => Some(Specifier::Delim(name)),
            "expr" => Some(Specifier::Expr(name)),
            "ident" => Some(Specifier::Ident(name)),
            "item" => Some(Specifier::Item(name)),
            "lftm" => Some(Specifier::Lftm(name)),
            "lit" => Some(Specifier::Lit(name)),
            "meta" => Some(Specifier::Meta(name)),
            "pat" => Some(Specifier::Pat(name)),
            "path" => Some(Specifier::Path(name)),
            "stmt" => Some(Specifier::Stmt(name)),
            "ty" => Some(Specifier::Ty(name)),
            "tok" => Some(Specifier::Tok(name)),
            "tt" => Some(Specifier::Tt(name)),
            _ => None,
        }
    }

    /// Constructs a specifier for a specific identifier.
    pub fn ident(ident: &str) -> Specifier {
        Specifier::Specific(Token::Ident(token::str_to_ident(ident)))
    }

    /// Constructs a specifier for a specific lifetime.
    pub fn lifetime(lifetime: &str) -> Specifier {
        Specifier::Specific(Token::Lifetime(token::str_to_ident(lifetime)))
    }

    //- Accessors --------------------------------

    /// Returns the identifier for this specifier, if any.
    pub fn get_ident(&self, context: &ExtCtxt) -> Option<Ident> {
        match *self {
            Specifier::Enum(_, ref enum_) => Some(context.ident_of(&enum_.name)),
            Specifier::Struct(_, ref struct_) => Some(context.ident_of(&struct_.name)),
            _ => None,
        }
    }

    /// Returns the name of this specifier, if any.
    pub fn get_name(&self) -> Option<&String> {
        match *self {
            Specifier::Attr(ref name) |
            Specifier::BinOp(ref name) |
            Specifier::Block(ref name) |
            Specifier::Delim(ref name) |
            Specifier::Expr(ref name) |
            Specifier::Ident(ref name) |
            Specifier::Item(ref name) |
            Specifier::Lftm(ref name) |
            Specifier::Lit(ref name) |
            Specifier::Meta(ref name) |
            Specifier::Pat(ref name) |
            Specifier::Path(ref name) |
            Specifier::Stmt(ref name) |
            Specifier::Ty(ref name) |
            Specifier::Tok(ref name) |
            Specifier::Tt(ref name) |
            Specifier::Extractor(ref name, _) |
            Specifier::Enum(ref name, _) |
            Specifier::Struct(ref name, _) => Some(name),
            Specifier::Sequence(ref name, _) => name.as_ref(),
            _ => None,
        }
    }
}

//================================================
// Structs
//================================================

// Enum __________________________________________

/// An enumerated argument specification.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Enum {
    /// The name of this specification.
    pub name: String,
    /// The variants defined by this specification.
    pub variants: Vec<Variant>,
}

impl Enum {
    //- Constructors -----------------------------

    /// Constructs a new `Enum`.
    pub fn new(name: String, variants: Vec<Variant>) -> Enum {
        Enum { name: name, variants: variants }
    }
}

// Delimited _____________________________________

/// A delimited piece of an argument specification.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Delimited {
    /// The type of delimiter that marks the borders of this delimited piece.
    pub delimiter: DelimToken,
    /// The argument specification in this delimited piece.
    pub specification: Vec<Specifier>,
}

impl Delimited {
    //- Constructors -----------------------------

    /// Constructs a new `Delimited`.
    pub fn new(delimiter: DelimToken, specification: Vec<Specifier>) -> Delimited {
        Delimited { delimiter: delimiter, specification: specification }
    }
}

// Extractor _____________________________________

/// A specifier that will be filtered through an extraction function.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Extractor {
    /// The specifier for the value that will filtered.
    pub specifier: Box<Specifier>,
    /// The name of the extractor function.
    pub extractor: String,
}

impl Extractor {
    //- Constructors -----------------------------

    /// Constructs a new `Extractor`.
    pub fn new(specifier: Box<Specifier>, extractor: String) -> Extractor {
        Extractor { specifier: specifier, extractor: extractor }
    }
}

// Sequence ______________________________________

/// A sequence piece of an argument specification.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sequence {
    /// The number of times this sequence piece is expected to occur.
    pub amount: Amount,
    /// The token that is expected to separate the occurrences of this sequence piece, if any.
    pub separator: Option<Token>,
    /// The argument specification for this sequence piece.
    pub specification: Vec<Specifier>,
}

impl Sequence {
    //- Constructors -----------------------------

    /// Constructs a new `Sequence`.
    pub fn new(
        amount: Amount, separator: Option<Token>, specification: Vec<Specifier>
    ) -> Sequence {
        Sequence { amount: amount, separator: separator, specification: specification }
    }
}

// Struct ________________________________________

/// A structured argument specification.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Struct {
    /// The name of this specification.
    pub name: String,
    /// The value of this specification.
    pub specification: Vec<Specifier>,
}

impl Struct {
    //- Constructors -----------------------------

    /// Constructs a new `Struct`.
    pub fn new(name: String, specification: Vec<Specifier>) -> Struct {
        Struct { name: name, specification: specification }
    }
}

// Variant _______________________________________

/// A variant defined by an enumerated argument specification.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Variant {
    /// The name of this variant.
    pub name: String,
    /// The value of this variant.
    pub specification: Vec<Specifier>,
}

impl Variant {
    //- Constructors -----------------------------

    /// Constructs a new `Variant`.
    pub fn new(name: String, specification: Vec<Specifier>) -> Variant {
        Variant { name: name, specification: specification }
    }
}

//================================================
// Functions
//================================================

struct State<'a> {
    specifications: &'a HashMap<String, Specification>,
    names: HashSet<String>,
}

/// Parses a simple named specifier.
fn parse_simple_specifier(
    span: Span, name: String, specifier: &str
) -> PluginResult<Specifier> {
    match Specifier::simple(name.clone(), specifier) {
        Some(specifier) => Ok(specifier),
        _ => if let Some(extractor) = extractor::EXTRACTORS.iter().find(|e| *e == &specifier) {
            let underscore = specifier.find('_').unwrap();
            let specifier = Specifier::simple(name.clone(), &specifier[..underscore]).unwrap();
            Ok(Specifier::Extractor(name, Extractor::new(Box::new(specifier), (*extractor).into())))
        } else {
            Err((span, "invalid named specifier type".into()))
        },
    }
}

/// Parses a sequence named specifier.
fn parse_sequence_specifier<'i, I: Iterator<Item=&'i TokenTree>>(
    span: Span, tts: &mut I, name: String, subtts: &[TokenTree]
) -> PluginResult<Specifier> {
    let specifications = HashMap::new();
    let mut state = State { specifications: &specifications, names: HashSet::new() };
    let sequence = try!(parse_sequence(span, tts, subtts, &mut state));
    if state.names.is_empty() {
        Ok(Specifier::Sequence(Some(name), sequence))
    } else {
        Err((span, "named specifiers are disallowed in named sequences".into()))
    }
}

/// Parses a named specifier.
fn parse_named_specifier<'a, 'i, I: Iterator<Item=&'i TokenTree>>(
    span: Span, tts: &mut I, name: String, state: &mut State<'a>
) -> PluginResult<Specifier> {
    match expect_tt!(span, tts) {
        &TokenTree::Token(_, Token::Colon) => { },
        tt => return Err((tt.span(), "expected `:`".into())),
    }
    match expect_tt!(span, tts) {
        &TokenTree::Token(_, Token::Dollar) => {
            let (subspan, specification) = match expect_tt!(span, tts) {
                &TokenTree::Token(subspan, Token::Ident(ident)) => (subspan, ident),
                tt => return Err((tt.span(), "expected specification".into())),
            };
            match state.specifications.get(&*specification.name.as_str()) {
                Some(specification) => match *specification {
                    Specification::Enum(ref enum_) =>
                        Ok(Specifier::Enum(name, enum_.clone())),
                    Specification::Struct(ref struct_) =>
                        Ok(Specifier::Struct(name, struct_.clone())),
                },
                _ => Err((subspan, "no such specification".into())),
            }
        },
        &TokenTree::Token(subspan, Token::Ident(ident)) =>
            parse_simple_specifier(subspan, name, &*ident.name.as_str()),
        &TokenTree::Delimited(subspan, ref delimited) => if delimited.delim == DelimToken::Paren {
            parse_sequence_specifier(subspan, tts, name, &delimited.tts)
        } else {
            Err((subspan, "expected named specifier specification".into()))
        },
        tt => Err((tt.span(), "expected named specifier specification".into())),
    }
}

/// Parses an unnamed sequence.
fn parse_sequence<'a, 'i, I: Iterator<Item=&'i TokenTree>>(
    span: Span, tts: &mut I, subtts: &[TokenTree], state: &mut State<'a>
) -> PluginResult<Sequence> {
    let specification = try!(parse_specifiers_impl(span, subtts, state));
    let (amount, separator) = match expect_tt!(span, tts) {
        &TokenTree::Token(_, Token::Question) => (Amount::ZeroOrOne, None),
        &TokenTree::Token(_, Token::BinOp(BinOpToken::Star)) => (Amount::ZeroOrMore, None),
        &TokenTree::Token(_, Token::BinOp(BinOpToken::Plus)) => (Amount::OneOrMore, None),
        &TokenTree::Token(_, ref separator) => match expect_tt!(span, tts) {
            &TokenTree::Token(_, Token::BinOp(BinOpToken::Star)) =>
                (Amount::ZeroOrMore, Some(separator.clone())),
            &TokenTree::Token(_, Token::BinOp(BinOpToken::Plus)) =>
                (Amount::OneOrMore, Some(separator.clone())),
            tt => return Err((tt.span(), "expected `*` or `+`".into())),
        },
        tt => return Err((tt.span(), "expected separator, `?`, `*`, or `+`".into())),
    };
    Ok(Sequence::new(amount, separator, specification))
}

/// Parses a named specifier or an unnamed sequence.
fn parse_specifier<'a, 'i, I: Iterator<Item=&'i TokenTree>>(
    span: Span, tts: &mut I, state: &mut State<'a>
) -> PluginResult<Specifier> {
    match expect_tt!(span, tts) {
        &TokenTree::Token(subspan, Token::Ident(ident)) => {
            let name = format!("{}", ident);
            if state.names.insert(name.clone()) {
                parse_named_specifier(span, tts, name, state)
            } else {
                Err((subspan, "duplicate named specifier".into()))
            }
        },
        &TokenTree::Delimited(subspan, ref delimited) => if delimited.delim == DelimToken::Paren {
            let sequence = try!(parse_sequence(span, tts, &delimited.tts, state));
            Ok(Specifier::Sequence(None, sequence))
        } else {
            Err((subspan, "expected named specifier or unnamed sequence".into()))
        },
        tt => Err((tt.span(), "expected named specifier or unnamed sequence".into())),
    }
}

/// Actually parses the supplied argument specifiers.
fn parse_specifiers_impl<'a>(
    span: Span, tts: &[TokenTree], state: &mut State<'a>
) -> PluginResult<Vec<Specifier>> {
    let mut tts = tts.iter();
    let mut specification = vec![];
    while let Some(tt) = tts.next() {
        let specifier = match *tt {
            TokenTree::Token(_, Token::Dollar) => try!(parse_specifier(span, &mut tts, state)),
            TokenTree::Token(_, ref token) => Specifier::Specific(token.clone()),
            TokenTree::Delimited(subspan, ref delimited) => {
                let specification = try!(parse_specifiers_impl(subspan, &delimited.tts, state));
                Specifier::Delimited(Delimited::new(delimited.delim, specification))
            },
            _ => panic!("{:?}", tt),
        };
        specification.push(specifier);
    }
    Ok(specification)
}

fn with_tts<T, F: Fn(&[TokenTree]) -> T>(name: &str, string: &str, f: F) -> T {
    let session = ParseSess::new();
    let name = name.into();
    let mut parser = parse::new_parser_from_source_str(&session, vec![], name, string.into());
    let tts = parser.parse_all_token_trees().unwrap();
    f(&tts)
}

/// Parses the supplied argument specifiers.
pub fn parse_specifiers(
    tts: &[TokenTree], specifications: &HashMap<String, Specification>
) -> PluginResult<Vec<Specifier>> {
    let mut state = State { specifications: specifications, names: HashSet::new() };
    parse_specifiers_impl(utility::span_tts(tts), tts, &mut state)
}

/// Parses the supplied argument specifiers string.
pub fn parse_specifiers_string(
    string: &str, specifications: &HashMap<String, Specification>
) -> PluginResult<Vec<Specifier>> {
    with_tts("<specifiers>", string, |tts| parse_specifiers(tts, specifications))
}

// Parses the body of an enumerated argument specification.
fn parse_specification_enum(
    name: String, tts: &[TokenTree], specifications: &HashMap<String, Specification>
) -> PluginResult<Specification> {
    let tts = if tts.get(tts.len() - 1).map_or(false, |tt| tt.eq_token(Token::Comma)) {
        &tts[..tts.len() - 1]
    } else {
        tts
    };
    let variants = tts.split(|tt| tt.eq_token(Token::Comma)).map(|tts| {
        if tts.len() == 2 {
            let mut tts = tts.iter();
            let name = expect_tt!(IDENTIFIER: DUMMY_SP, tts);
            let tts = expect_tt!(DELIMITED: DUMMY_SP, tts);
            Ok(Variant::new(name, try!(parse_specifiers(&tts, specifications))))
        } else {
            Err((DUMMY_SP, "invalid specification variant".into()))
        }
    }).collect::<Result<Vec<_>, _>>();
    Ok(Specification::Enum(Enum::new(name, try!(variants))))
}

// Parses the body of a structured argument specification.
fn parse_specification_struct(
    name: String, tts: &[TokenTree], specifications: &HashMap<String, Specification>
) -> PluginResult<Specification> {
    let specification = try!(parse_specifiers(tts, specifications));
    Ok(Specification::Struct(Struct::new(name, specification)))
}

/// Parses the supplied argument specification.
pub fn parse_specification(
    tts: &[TokenTree], specifications: &HashMap<String, Specification>
) -> PluginResult<Specification> {
    let span = utility::span_tts(tts);
    let mut tts = tts.iter();
    let enum_ = match expect_tt!(span, tts) {
        &TokenTree::Token(_, Token::Ident(ident)) if ident.name.as_str() == "enum" => true,
        &TokenTree::Token(_, Token::Ident(ident)) if ident.name.as_str() == "struct" => false,
        tt => return Err((tt.span(), "expected `enum` or `struct`".into())),
    };
    let name = expect_tt!(IDENTIFIER: span, tts);
    let tts = expect_tt!(DELIMITED: span, tts);
    if enum_ {
        parse_specification_enum(name, tts, specifications)
    } else {
        parse_specification_struct(name, tts, specifications)
    }
}

/// Parses the supplied argument specification string.
pub fn parse_specification_string(
    string: &str, specifications: &HashMap<String, Specification>
) -> PluginResult<Specification> {
    with_tts("<specification>", string, |tts| parse_specification(tts, specifications))
}
