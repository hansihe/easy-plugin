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

use easy_plugin_parsers::{PluginResult};
use easy_plugin_parsers::arguments::*;
use easy_plugin_parsers::specification::{Specification, Specifier, Struct};
use easy_plugin_parsers::specification::{parse_specification_string, parse_specifiers_string};

use syntax::print::pprust;
use syntax::ast::*;
use syntax::codemap::{BytePos, Spanned};
use syntax::ext::base::{DummyResolver, ExtCtxt};
use syntax::ext::expand::{ExpansionConfig};
use syntax::parse::{self, ParseSess};
use syntax::parse::token::{BinOpToken, DelimToken, Token};
use syntax::ptr::{P};
use syntax::tokenstream::{Delimited, TokenTree};

macro_rules! parse_specification {
    ([$($name:expr => $value:expr), +,], $specifiers:expr) => ({
        let mut specifications = HashMap::new();
        $(let specification = parse_specification_string($value, &specifications).unwrap();
        specifications.insert($name.into(), specification);)+
        parse_specifiers_string($specifiers, &specifications).unwrap()
    });
}

macro_rules! assert_span_eq {
    ($span:expr, $lo:expr, $hi:expr) => ({
        let lo = BytePos($lo);
        let hi = BytePos($hi);
        if $span.lo != lo || $span.hi != hi {
            println!("");
            println!("= Expected =========");
            println!("{:?}, {:?}", lo, hi);
            println!("= Generated ========");
            println!("{:?}, {:?}", $span.lo, $span.hi);
            panic!();
        }
    });
}

fn parse(specifiers: &[Specifier], arguments: &str) -> PluginResult<Arguments> {
    let session = ParseSess::new();
    let name = "<arguments>".into();
    let mut parser = parse::new_parser_from_source_str(&session, vec![], name, arguments.into());
    let tts = parser.parse_all_token_trees().unwrap();
    let specification = Specification::Struct(Struct::new("Struct".into(), specifiers.to_vec()));

    let config = ExpansionConfig::default("".into());
    let mut resolver = DummyResolver;
    let context = ExtCtxt::new(&session, vec![], config, &mut resolver);
    parse_arguments(&context, &tts, &specification)
}

fn parse_string(specifiers: &str, arguments: &str) -> PluginResult<Arguments> {
    let specifications = HashMap::new();
    let specifiers = parse_specifiers_string(specifiers, &specifications).unwrap();
    parse(&specifiers, arguments)
}

#[test]
fn test_parse_arguments_error() {
    macro_rules! assert_error_eq {
        ($specification:expr, $string:expr, $lo:expr, $hi:expr, $message:expr) => ({
            let lo = BytePos($lo);
            let hi = BytePos($hi);
            match parse_string($specification, $string) {
                Err((span, message)) => if span.lo != lo || span.hi != hi || message != $message {
                    println!("");
                    println!("= Expected =========");
                    println!("{:?}, {:?}: {:?}", lo, hi, $message);
                    println!("= Generated ========");
                    println!("{:?}, {:?}: {:?}", span.lo, span.hi, message);
                    panic!();
                },
                _ => panic!("expected error"),
            }
        });
    }

    assert_error_eq!("", "foo", 0, 3, "too many arguments");
    assert_error_eq!("$a:ident", "foo bar", 4, 7, "too many arguments");

    macro_rules! assert_unexpected_error_eq {
        ($specification:expr, $description:expr) => ({
            let error = concat!("unexpected end of arguments: expected ", $description, ": 'a'");
            assert_error_eq!($specification, "", 0, 0, error);
            assert_error_eq!(concat!("$b:ident ", $specification), "foo", 0, 3, error);
        });
    }

    assert_unexpected_error_eq!("$a:attr", "attribute");
    assert_unexpected_error_eq!("$a:binop", "binary operator");
    assert_unexpected_error_eq!("$a:block", "block");
    assert_unexpected_error_eq!("$a:delim", "opening delimiter");
    assert_unexpected_error_eq!("$a:expr", "expression");
    assert_unexpected_error_eq!("$a:ident", "identifier");
    assert_unexpected_error_eq!("$a:item", "item");
    assert_unexpected_error_eq!("$a:lftm", "lifetime");
    assert_unexpected_error_eq!("$a:lit", "literal");
    assert_unexpected_error_eq!("$a:meta", "meta item");
    assert_unexpected_error_eq!("$a:pat", "pattern");
    assert_unexpected_error_eq!("$a:path", "path");
    assert_unexpected_error_eq!("$a:stmt", "statement");
    assert_unexpected_error_eq!("$a:ty", "type");
    assert_unexpected_error_eq!("$a:tok", "token");
    assert_unexpected_error_eq!("$a:tt", "token tree");

    assert_unexpected_error_eq!("$a:attr_list", "attribute");
    assert_error_eq!("$a:attr_list", "#[test]", 0, 7, "expected `MetaItemKind::List` attribute");

    assert_unexpected_error_eq!("$a:ty_vec", "type");
    assert_error_eq!("$a:ty_vec", "&[i32]", 0, 6, "expected `TyKind::Vec` type");

    assert_error_eq!("foo + bar", "", 0, 0, "unexpected end of arguments: expected `foo`");
    assert_error_eq!("foo + bar", "bar", 0, 3, "expected `foo`");
    assert_error_eq!("foo + bar", "foo", 0, 3, "unexpected end of arguments: expected `+`");
    assert_error_eq!("foo + bar", "foo -", 4, 5, "expected `+`");
    assert_error_eq!("foo + bar", "foo +", 0, 5, "unexpected end of arguments: expected `bar`");
    assert_error_eq!("foo + bar", "foo + foo", 6, 9, "expected `bar`");

    assert_error_eq!("()", "", 0, 0, "unexpected end of arguments: expected `(`");
    assert_error_eq!("(foo)", "[foo]", 0, 1, "expected `(`");
    assert_error_eq!("(foo)", "()", 1, 2, "expected `foo`");
    assert_error_eq!("(foo)", "(bar)", 1, 4, "expected `foo`");

    assert_unexpected_error_eq!("$($a:attr)+", "attribute");
    assert_unexpected_error_eq!("$($a:attr_list)+", "attribute");
    assert_error_eq!("$(foo)+", "", 0, 0, "unexpected end of arguments: expected `foo`");

    assert_error_eq!("$a:(foo)+", "", 0, 0, "unexpected end of arguments: expected `foo`");
}

#[test]
fn test_parse_arguments_empty() {
    parse_string("", "").unwrap();
}

#[test]
fn test_parse_arguments_simple() {
    let argument = parse_string("$a:attr", "#[test]").unwrap().get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[test]");
    assert_span_eq!(argument.span, 0, 7);

    let argument = parse_string("$a:binop", "+").unwrap().get::<Spanned<BinOpToken>>("a");
    assert_eq!(argument.node, BinOpToken::Plus);
    assert_span_eq!(argument.span, 0, 1);

    let argument = parse_string("$a:block", "{ let foo = 322; }").unwrap().get::<P<Block>>("a");
    assert_eq!(pprust::block_to_string(&argument), "{ let foo = 322; }");
    assert_span_eq!(argument.span, 0, 18);

    let argument = parse_string("$a:delim", "[17, 322]").unwrap().get::<Spanned<Delimited>>("a");
    assert_eq!(argument.node.delim, DelimToken::Bracket);
    assert_eq!(pprust::tts_to_string(&argument.node.tts), "17 , 322");
    assert_span_eq!(argument.span, 0, 9);

    let argument = parse_string("$a:expr", "4 * 17").unwrap().get::<P<Expr>>("a");
    assert_eq!(pprust::expr_to_string(&argument), "4 * 17");
    assert_span_eq!(argument.span, 0, 6);

    let argument = parse_string("$a:ident", "foo").unwrap().get::<Spanned<Ident>>("a");
    assert_eq!(argument.node.to_string(), "foo");
    assert_span_eq!(argument.span, 0, 3);

    let argument = parse_string("$a:item", "struct Struct;").unwrap().get::<P<Item>>("a");
    assert_eq!(pprust::item_to_string(&argument), "struct Struct;");
    assert_span_eq!(argument.span, 0, 14);

    let argument = parse_string("$a:lftm", "'foo").unwrap().get::<Spanned<Name>>("a");
    assert_eq!(argument.node.to_string(), "'foo");
    assert_span_eq!(argument.span, 0, 4);

    let argument = parse_string("$a:lit", "322u32").unwrap().get::<Lit>("a");
    assert_eq!(pprust::lit_to_string(&argument), "322u32");
    assert_span_eq!(argument.span, 0, 6);

    let argument = parse_string("$a:meta", "foo(bar)").unwrap().get::<P<MetaItem>>("a");
    assert_eq!(pprust::meta_item_to_string(&argument), "foo(bar)");
    assert_span_eq!(argument.span, 0, 8);

    let argument = parse_string("$a:pat", "(ref foo, ref mut bar)").unwrap().get::<P<Pat>>("a");
    assert_eq!(pprust::pat_to_string(&argument), "(ref foo, ref mut bar)");
    assert_span_eq!(argument.span, 0, 22);

    let argument = parse_string("$a:path", "std::vec::Vec<i32>").unwrap().get::<Path>("a");
    assert_eq!(pprust::path_to_string(&argument), "std::vec::Vec<i32>");
    assert_span_eq!(argument.span, 0, 18);

    let argument = parse_string("$a:stmt", "let foo = 322").unwrap().get::<Stmt>("a");
    assert_eq!(pprust::stmt_to_string(&argument), "let foo = 322;");
    assert_span_eq!(argument.span, 0, 13);

    let argument = parse_string("$a:ty", "i32").unwrap().get::<P<Ty>>("a");
    assert_eq!(pprust::ty_to_string(&argument), "i32");
    assert_span_eq!(argument.span, 0, 3);

    let argument = parse_string("$a:tok", "!").unwrap().get::<Spanned<Token>>("a");
    assert_eq!(argument.node, Token::Not);
    assert_span_eq!(argument.span, 0, 1);

    let argument = parse_string("$a:tt", "!").unwrap().get::<TokenTree>("a");
    assert_eq!(pprust::tt_to_string(&argument), "!");
    assert_span_eq!(argument.span(), 0, 1);
}

#[test]
fn test_parse_arguments_extractor() {
    let arguments = parse_string("$a:attr_name_value", "#[foo=\"bar\"]").unwrap();
    let (name, value) = arguments.get::<(String, Lit)>("a");
    assert_eq!(name, "foo");
    assert_eq!(pprust::lit_to_string(&value), "\"bar\"");

    let argument = parse_string("$a:ty_vec", "[i32]").unwrap().get::<P<Ty>>("a");
    assert_eq!(pprust::ty_to_string(&argument), "i32");
}

#[test]
fn test_parse_arguments_specific() {
    parse_string("foo + bar", "foo + bar").unwrap();
}

#[test]
fn test_parse_arguments_delimited() {
    parse_string("()", "()").unwrap();

    let argument = parse_string("($a:attr)", "(#[test])").unwrap().get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[test]");
    assert_span_eq!(argument.span, 1, 8);

    let argument = parse_string("($a:attr_name_value)", "(#[foo=\"bar\"])").unwrap();
    let (name, value) = argument.get::<(String, Lit)>("a");
    assert_eq!(name, "foo");
    assert_eq!(pprust::lit_to_string(&value), "\"bar\"");

    parse_string("(foo + bar)", "(foo + bar)").unwrap();

    let arguments = parse_string("($($a:attr)?)", "(#[test])").unwrap();
    let arguments = arguments.get_sequence("a").to_option::<Attribute>().unwrap();
    assert_eq!(pprust::attribute_to_string(&arguments), "#[test]");
    assert_span_eq!(arguments.span, 1, 8);

    assert_eq!(parse_string("($a:(foo)?)", "(foo)").unwrap().get::<Spanned<bool>>("a").node, true);
}

#[test]
fn test_parse_arguments_sequence() {
    parse_string("$()?", "").unwrap();
    parse_string("$()*", "").unwrap();
    parse_string("$()+", "").unwrap();

    let arguments = parse_string("$($a:attr)?", "").unwrap();
    let arguments = arguments.get_sequence("a").to_option::<Attribute>();
    assert_eq!(arguments, None);

    let arguments = parse_string("$($a:attr)?", "#[test]").unwrap();
    let arguments = arguments.get_sequence("a").to_option::<Attribute>().unwrap();
    assert_eq!(pprust::attribute_to_string(&arguments), "#[test]");
    assert_span_eq!(arguments.span, 0, 7);

    let arguments = parse_string("$($a:attr)*", "").unwrap();
    let arguments = arguments.get_sequence("a").to_vec::<Attribute>();
    assert_eq!(arguments.len(), 0);

    let arguments = parse_string("$($a:attr)*", "#[test]").unwrap();
    let arguments = arguments.get_sequence("a").to_vec::<Attribute>();
    assert_eq!(arguments.len(), 1);
    assert_eq!(pprust::attribute_to_string(&arguments[0]), "#[test]");
    assert_span_eq!(arguments[0].span, 0, 7);

    let arguments = parse_string("$($a:attr)*", "#[test] #[foo(bar, baz)]").unwrap();
    let arguments = arguments.get_sequence("a").to_vec::<Attribute>();
    assert_eq!(arguments.len(), 2);
    assert_eq!(pprust::attribute_to_string(&arguments[0]), "#[test]");
    assert_span_eq!(arguments[0].span, 0, 7);
    assert_span_eq!(arguments[1].span, 8, 24);

    let arguments = parse_string("$($a:attr)+", "#[test]").unwrap();
    let arguments = arguments.get_sequence("a").to_vec::<Attribute>();
    assert_eq!(arguments.len(), 1);
    assert_eq!(pprust::attribute_to_string(&arguments[0]), "#[test]");
    assert_span_eq!(arguments[0].span, 0, 7);

    let arguments = parse_string("$($a:attr)+", "#[test] #[foo(bar, baz)]").unwrap();
    let arguments = arguments.get_sequence("a").to_vec::<Attribute>();
    assert_eq!(arguments.len(), 2);

    assert_eq!(pprust::attribute_to_string(&arguments[0]), "#[test]");
    assert_span_eq!(arguments[0].span, 0, 7);

    assert_eq!(pprust::attribute_to_string(&arguments[1]), "#[foo(bar, baz)]");
    assert_span_eq!(arguments[1].span, 8, 24);

    let specification = parse_specification!([
        "Enum" => "enum Enum { A { $a:attr }, B { $b:binop } }",
    ], "$($a:$Enum)+");
    let arguments = parse(&specification, "#[test] + #[foo(bar, baz)] -").unwrap();
    let arguments = arguments.get_sequence("a").to_arguments_vec(|a| a);
    assert_eq!(arguments.len(), 4);

    assert_eq!(arguments[0].variant, Some(0));
    let argument = arguments[0].get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[test]");
    assert_span_eq!(argument.span, 0, 7);

    assert_eq!(arguments[1].variant, Some(1));
    let argument = arguments[1].get::<Spanned<BinOpToken>>("b");
    assert_eq!(argument.node, BinOpToken::Plus);
    assert_span_eq!(argument.span, 8, 9);

    assert_eq!(arguments[2].variant, Some(0));
    let argument = arguments[2].get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[foo(bar, baz)]");
    assert_span_eq!(argument.span, 10, 26);

    assert_eq!(arguments[3].variant, Some(1));
    let argument = arguments[3].get::<Spanned<BinOpToken>>("b");
    assert_eq!(argument.node, BinOpToken::Minus);
    assert_span_eq!(argument.span, 27, 28);

    let arguments = parse_string("$($($a:attr), *), *", "#[test]").unwrap();
    let arguments = arguments.get_sequence("a").to_sequence_vec(|s| s.to_vec::<Attribute>());
    assert_eq!(arguments.len(), 1);
    assert_eq!(arguments[0].len(), 1);
    assert_eq!(pprust::attribute_to_string(&arguments[0][0]), "#[test]");
    assert_span_eq!(arguments[0][0].span, 0, 7);

    let arguments = parse_string("$($a:ty $($b:ty)?), *", "i32, i32 f32, i32").unwrap();
    let arguments = arguments.get_sequence("b").to_sequence_vec(|s| s.to_option::<P<Ty>>());
    assert_eq!(arguments.len(), 3);
    assert!(arguments[0].is_none());
    assert!(arguments[1].is_some());
    assert!(arguments[2].is_none());

    let arguments = parse_string("$($a:ty $($b:ty)*), *", "i32, i32 f32, i32").unwrap();
    let arguments = arguments.get_sequence("b").to_sequence_vec(|s| s.to_vec::<P<Ty>>());
    assert_eq!(arguments[0].len(), 0);
    assert_eq!(arguments[1].len(), 1);
    assert_eq!(arguments[2].len(), 0);
}

#[test]
fn test_parse_arguments_named_sequence() {
    assert_eq!(parse_string("$a:()?", "").unwrap().get::<Spanned<bool>>("a").node, false);
    assert_eq!(parse_string("$a:()*", "").unwrap().get::<Spanned<usize>>("a").node, 0);
    assert_eq!(parse_string("$a:()+", "").unwrap().get::<Spanned<usize>>("a").node, 0);

    assert_eq!(parse_string("$a:(foo)?", "").unwrap().get::<Spanned<bool>>("a").node, false);
    assert_eq!(parse_string("$a:(foo)?", "foo").unwrap().get::<Spanned<bool>>("a").node, true);
    assert_eq!(parse_string("$a:(foo)*", "").unwrap().get::<Spanned<usize>>("a").node, 0);
    assert_eq!(parse_string("$a:(foo)*", "foo").unwrap().get::<Spanned<usize>>("a").node, 1);
    assert_eq!(parse_string("$a:(foo)*", "foo foo").unwrap().get::<Spanned<usize>>("a").node, 2);
    assert_eq!(parse_string("$a:(foo)+", "foo").unwrap().get::<Spanned<usize>>("a").node, 1);
    assert_eq!(parse_string("$a:(foo)+", "foo foo").unwrap().get::<Spanned<usize>>("a").node, 2);
}

#[test]
fn test_parse_arguments_enum() {
    let specification = parse_specification!([
        "Enum" => "enum Enum { A { $a:attr }, B { $b:binop } }",
    ], "$a:$Enum");

    let arguments = parse(&specification, "#[test]").unwrap();
    let arguments = arguments.get_arguments("a");
    assert_eq!(arguments.variant, Some(0));
    let argument = arguments.get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[test]");
    assert_span_eq!(argument.span, 0, 7);

    let arguments = parse(&specification, "+").unwrap();
    let arguments = arguments.get_arguments("a");
    assert_eq!(arguments.variant, Some(1));
    let argument = arguments.get::<Spanned<BinOpToken>>("b");
    assert_eq!(argument.node, BinOpToken::Plus);
    assert_span_eq!(argument.span, 0, 1);
}

#[test]
fn test_parse_arguments_struct() {
    let specification = parse_specification!([
        "Struct" => "struct Struct { $a:attr $b:binop }",
    ], "$a:$Struct");

    let arguments = parse(&specification, "#[test] +").unwrap();
    let arguments = arguments.get_arguments("a");
    assert_eq!(arguments.variant, None)
    ;
    let argument = arguments.get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[test]");
    assert_span_eq!(argument.span, 0, 7);

    let argument = arguments.get::<Spanned<BinOpToken>>("b");
    assert_eq!(argument.node, BinOpToken::Plus);
    assert_span_eq!(argument.span, 8, 9);
}
