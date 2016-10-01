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

#![cfg_attr(not(feature="syntex"), feature(rustc_private))]

#[cfg(feature="syntex")]
extern crate syntex_syntax as syntax;
#[cfg(not(feature="syntex"))]
extern crate syntax;

extern crate easy_plugin_parsers;

use std::collections::{HashMap};

use easy_plugin_parsers::specification::*;

use syntax::parse::token::{DelimToken, Token};

macro_rules! spec {
    ($($variant:ident($($tt:tt)*)), *) => (vec![$(Specifier::$variant($($tt)*)), *]);
}

fn parse(string: &str) -> Vec<Specifier> {
    let specifications = HashMap::new();
    parse_specifiers_string(string, &specifications).unwrap()
}

#[test]
fn test_parse_specification_empty() {
    assert_eq!(parse(""), spec![]);
}

#[test]
fn test_parse_specification_simple() {
    macro_rules! assert_simple_eq {
        ($specifier:expr, $variant:ident) => ({
            assert_eq!(parse(concat!("$a:", $specifier)), spec![$variant("a".into())]);
        });
    }

    assert_simple_eq!("attr", Attr);
    assert_simple_eq!("binop", BinOp);
    assert_simple_eq!("block", Block);
    assert_simple_eq!("delim", Delim);
    assert_simple_eq!("expr", Expr);
    assert_simple_eq!("ident", Ident);
    assert_simple_eq!("item", Item);
    assert_simple_eq!("lftm", Lftm);
    assert_simple_eq!("lit", Lit);
    assert_simple_eq!("meta", Meta);
    assert_simple_eq!("pat", Pat);
    assert_simple_eq!("path", Path);
    assert_simple_eq!("stmt", Stmt);
    assert_simple_eq!("ty", Ty);
    assert_simple_eq!("tok", Tok);
    assert_simple_eq!("tt", Tt);
}

#[test]
fn test_parse_specification_extractor() {
    macro_rules! assert_extractor_eq {
        ($specifier:expr, $variant:ident) => ({
            let specifier = Box::new(Specifier::$variant("a".into()));
            let extractor = Extractor::new(specifier, $specifier.into());
            assert_eq!(parse(concat!("$a:", $specifier)), spec![Extractor("a".into(), extractor)]);
        });
    }

    assert_extractor_eq!("attr_list", Attr);
    assert_extractor_eq!("expr_addr_of", Expr);
    assert_extractor_eq!("item_const", Item);
    assert_extractor_eq!("lit_bool", Lit);
    assert_extractor_eq!("meta_list", Meta);
    assert_extractor_eq!("pat_box", Pat);
    assert_extractor_eq!("stmt_expr", Stmt);
    assert_extractor_eq!("ty_bare_fn", Ty);
    assert_extractor_eq!("tok_and_and", Tok);
    assert_extractor_eq!("tt_delimited", Tt);
}

#[test]
fn test_parse_specification_specific() {
    assert_eq!(parse("<"), spec![Specific(Token::Lt)]);
    assert_eq!(parse("="), spec![Specific(Token::Eq)]);
    assert_eq!(parse(">"), spec![Specific(Token::Gt)]);

    assert_eq!(parse("foo"), spec![ident("foo")]);
    assert_eq!(parse("'bar"), spec![lifetime("'bar")]);
}

#[test]
fn test_parse_specification_delimited() {
    macro_rules! assert_delimited_eq {
        ($string:expr, $delimiter:expr, $specification:expr) => ({
            let delimited = Delimited::new($delimiter, $specification);
            assert_eq!(parse($string), spec![Delimited(delimited)]);
        });
    }

    assert_delimited_eq!("{}", DelimToken::Brace, spec![]);
    assert_delimited_eq!("[]", DelimToken::Bracket, spec![]);
    assert_delimited_eq!("()", DelimToken::Paren, spec![]);

    assert_delimited_eq!("($a:attr)", DelimToken::Paren, spec![Attr("a".into())]);

    assert_delimited_eq!("(=)", DelimToken::Paren, spec![Specific(Token::Eq)]);

    assert_delimited_eq!("(foo)", DelimToken::Paren, spec![ident("foo")]);

    let sequence = Sequence::new(Amount::ZeroOrOne, None, spec![]);
    assert_delimited_eq!("($()?)", DelimToken::Paren, spec![Sequence(None, sequence)]);

    let delimited = Delimited::new(DelimToken::Paren, spec![]);
    let sequence = Sequence::new(Amount::ZeroOrOne, None, spec![Delimited(delimited)]);
    assert_delimited_eq!("($(())?)", DelimToken::Paren, spec![Sequence(None, sequence)]);

    let name = Some("a".into());
    let sequence = Sequence::new(Amount::ZeroOrOne, None, spec![]);
    assert_delimited_eq!("($a:()?)", DelimToken::Paren, spec![Sequence(name, sequence)]);
}

#[test]
fn test_parse_specification_sequence() {
    macro_rules! assert_sequence_eq {
        ($string:expr, $amount:expr, $separator:expr, $specification:expr) => ({
            let sequence = Sequence::new($amount, $separator, $specification);
            assert_eq!(parse($string), spec![Sequence(None, sequence)]);
        });
    }

    assert_sequence_eq!("$()?", Amount::ZeroOrOne, None, spec![]);
    assert_sequence_eq!("$()*", Amount::ZeroOrMore, None, spec![]);
    assert_sequence_eq!("$()+", Amount::OneOrMore, None, spec![]);

    assert_sequence_eq!("$(), *", Amount::ZeroOrMore, Some(Token::Comma), spec![]);
    assert_sequence_eq!("$(), +", Amount::OneOrMore, Some(Token::Comma), spec![]);

    assert_sequence_eq!("$($a:attr)?", Amount::ZeroOrOne, None, spec![Attr("a".into())]);

    assert_sequence_eq!("$(=)?", Amount::ZeroOrOne, None, spec![Specific(Token::Eq)]);

    assert_sequence_eq!("$(foo)?", Amount::ZeroOrOne, None, spec![ident("foo")]);

    let delimited = Delimited::new(DelimToken::Paren, spec![]);
    assert_sequence_eq!("$(())?", Amount::ZeroOrOne, None, spec![Delimited(delimited)]);

    let sequence = Sequence::new(Amount::ZeroOrOne, None, spec![]);
    let delimited = Delimited::new(DelimToken::Paren, spec![Sequence(None, sequence)]);
    assert_sequence_eq!("$(($()?))?", Amount::ZeroOrOne, None, spec![Delimited(delimited)]);

    let name = Some("a".into());
    let sequence = Sequence::new(Amount::ZeroOrOne, None, spec![]);
    assert_sequence_eq!("$($a:()?)?", Amount::ZeroOrOne, None, spec![Sequence(name, sequence)]);
}

#[test]
fn test_parse_specification_named_sequence() {
    macro_rules! assert_sequence_eq {
        ($string:expr, $amount:expr, $separator:expr, $specification:expr) => ({
            let sequence = Sequence::new($amount, $separator, $specification);
            assert_eq!(parse($string), spec![Sequence(Some("a".into()), sequence)]);
        });
    }

    assert_sequence_eq!("$a:()?", Amount::ZeroOrOne, None, spec![]);
    assert_sequence_eq!("$a:()*", Amount::ZeroOrMore, None, spec![]);
    assert_sequence_eq!("$a:()+", Amount::OneOrMore, None, spec![]);

    assert_sequence_eq!("$a:(), *", Amount::ZeroOrMore, Some(Token::Comma), spec![]);
    assert_sequence_eq!("$a:(), +", Amount::OneOrMore, Some(Token::Comma), spec![]);

    assert_sequence_eq!("$a:(=)?", Amount::ZeroOrOne, None, spec![Specific(Token::Eq)]);

    assert_sequence_eq!("$a:(foo)?", Amount::ZeroOrOne, None, spec![ident("foo")]);

    let delimited = Delimited::new(DelimToken::Paren, spec![]);
    assert_sequence_eq!("$a:(())?", Amount::ZeroOrOne, None, spec![Delimited(delimited)]);

    let sequence = Sequence::new(Amount::ZeroOrOne, None, spec![]);
    assert_sequence_eq!("$a:($()?)?", Amount::ZeroOrOne, None, spec![Sequence(None, sequence)]);
}

#[test]
fn test_parse_specification_enum() {
    let mut specifications = HashMap::new();
    let specification = parse_specification_string(r#"
        enum Enum {
            A { $a:attr },
            B { $b:ty },
        }
    "#, &specifications).unwrap();

    specifications.insert("Enum".into(), specification);
    let specification = parse_specifiers_string("$a:$Enum", &specifications).unwrap();
    assert_eq!(specification.len(), 1);
    match specification[0] {
        Specifier::Enum(ref name, ref enum_) => {
            assert_eq!(name, "a");
            assert_eq!(enum_.name, "Enum");
            assert_eq!(enum_.variants.len(), 2);
            assert_eq!(enum_.variants[0].name, "A");
            assert_eq!(enum_.variants[0].specification, parse("$a:attr"));
            assert_eq!(enum_.variants[1].name, "B");
            assert_eq!(enum_.variants[1].specification, parse("$b:ty"));
        },
        _ => panic!("expected enumerated specifier"),
    }
}

#[test]
fn test_parse_specification_struct() {
    let mut specifications = HashMap::new();
    let specification = parse_specification_string(r#"
        struct Struct {
            $a:attr $b:ty
        }
    "#, &specifications).unwrap();

    specifications.insert("Struct".into(), specification);
    let specification = parse_specifiers_string("$a:$Struct", &specifications).unwrap();
    assert_eq!(specification.len(), 1);
    match specification[0] {
        Specifier::Struct(ref name, ref struct_) => {
            assert_eq!(name, "a");
            assert_eq!(struct_.name, "Struct");
            assert_eq!(struct_.specification, parse("$a:attr $b:ty"));
        },
        _ => panic!("expected structured specifier"),
    }
}
