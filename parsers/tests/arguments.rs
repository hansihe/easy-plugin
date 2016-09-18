#![cfg_attr(not(feature="syntex"), feature(rustc_private))]

#[cfg(feature="syntex")]
extern crate syntex_syntax as syntax;
#[cfg(not(feature="syntex"))]
extern crate syntax;

extern crate easy_plugin_parsers;

use easy_plugin_parsers::specification;
use easy_plugin_parsers::{PluginResult};
use easy_plugin_parsers::arguments::*;

use syntax::print::pprust;
use syntax::ast::*;
use syntax::codemap::{BytePos, Spanned};
use syntax::parse::{self, ParseSess};
use syntax::parse::token::{BinOpToken, DelimToken, Token};
use syntax::ptr::{P};
use syntax::tokenstream::{Delimited, TokenTree};

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

fn parse(specification: &str, string: &str) -> PluginResult<Arguments> {
    let specification = specification::parse_specification_string(specification).unwrap();
    let session = ParseSess::new();
    let name = "<arguments>".into();
    let mut parser = parse::new_parser_from_source_str(&session, vec![], name, string.into());
    let tts = parser.parse_all_token_trees().unwrap();
    parse_arguments(&session, &tts, &specification)
}

#[test]
fn test_parse_arguments_error() {
    macro_rules! assert_error_eq {
        ($specification:expr, $string:expr, $lo:expr, $hi:expr, $message:expr) => ({
            let lo = BytePos($lo);
            let hi = BytePos($hi);
            match parse($specification, $string) {
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
    //assert_error_eq!("$a:attr_list", "#[test]", 0, 7, "expected `MetaItemKind::List` attribute");

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
    parse("", "").unwrap();
}

#[test]
fn test_parse_arguments_simple() {
    let argument = parse("$a:attr", "#[test]").unwrap().get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[test]");
    //assert_span_eq!(argument.span, 0, 7);

    let argument = parse("$a:binop", "+").unwrap().get::<Spanned<BinOpToken>>("a");
    assert_eq!(argument.node, BinOpToken::Plus);
    assert_span_eq!(argument.span, 0, 1);

    let argument = parse("$a:block", "{ let foo = 322; }").unwrap().get::<P<Block>>("a");
    assert_eq!(pprust::block_to_string(&argument), "{ let foo = 322; }");
    assert_span_eq!(argument.span, 0, 18);

    let argument = parse("$a:delim", "[17, 322]").unwrap().get::<Spanned<Delimited>>("a");
    assert_eq!(argument.node.delim, DelimToken::Bracket);
    assert_eq!(pprust::tts_to_string(&argument.node.tts), "17 , 322");
    assert_span_eq!(argument.span, 0, 9);

    let argument = parse("$a:expr", "4 * 17").unwrap().get::<P<Expr>>("a");
    assert_eq!(pprust::expr_to_string(&argument), "4 * 17");
    assert_span_eq!(argument.span, 0, 6);

    let argument = parse("$a:ident", "foo").unwrap().get::<Spanned<Ident>>("a");
    assert_eq!(argument.node.to_string(), "foo");
    assert_span_eq!(argument.span, 0, 3);

    let argument = parse("$a:item", "struct Struct;").unwrap().get::<P<Item>>("a");
    assert_eq!(pprust::item_to_string(&argument), "struct Struct;");
    assert_span_eq!(argument.span, 0, 14);

    let argument = parse("$a:lftm", "'foo").unwrap().get::<Spanned<Name>>("a");
    assert_eq!(argument.node.to_string(), "'foo");
    assert_span_eq!(argument.span, 0, 4);

    let argument = parse("$a:lit", "322u32").unwrap().get::<Lit>("a");
    assert_eq!(pprust::lit_to_string(&argument), "322u32");
    assert_span_eq!(argument.span, 0, 6);

    let argument = parse("$a:meta", "foo(bar)").unwrap().get::<P<MetaItem>>("a");
    assert_eq!(pprust::meta_item_to_string(&argument), "foo(bar)");
    assert_span_eq!(argument.span, 0, 8);

    let argument = parse("$a:pat", "(ref foo, ref mut bar)").unwrap().get::<P<Pat>>("a");
    assert_eq!(pprust::pat_to_string(&argument), "(ref foo, ref mut bar)");
    assert_span_eq!(argument.span, 0, 22);

    let argument = parse("$a:path", "std::vec::Vec<i32>").unwrap().get::<Path>("a");
    assert_eq!(pprust::path_to_string(&argument), "std::vec::Vec<i32>");
    assert_span_eq!(argument.span, 0, 18);

    let argument = parse("$a:stmt", "let foo = 322").unwrap().get::<Stmt>("a");
    assert_eq!(pprust::stmt_to_string(&argument), "let foo = 322;");
    assert_span_eq!(argument.span, 0, 13);

    let argument = parse("$a:ty", "i32").unwrap().get::<P<Ty>>("a");
    assert_eq!(pprust::ty_to_string(&argument), "i32");
    assert_span_eq!(argument.span, 0, 3);

    let argument = parse("$a:tok", "!").unwrap().get::<Spanned<Token>>("a");
    assert_eq!(argument.node, Token::Not);
    assert_span_eq!(argument.span, 0, 1);

    let argument = parse("$a:tt", "!").unwrap().get::<TokenTree>("a");
    assert_eq!(pprust::tt_to_string(&argument), "!");
    assert_span_eq!(argument.span(), 0, 1);
}

#[test]
fn test_parse_arguments_extractor() {
    let arguments = parse("$a:attr_name_value", "#[foo=\"bar\"]").unwrap();
    let (name, value) = arguments.get::<(String, Lit)>("a");
    assert_eq!(name, "foo");
    assert_eq!(pprust::lit_to_string(&value), "\"bar\"");

    let argument = parse("$a:ty_vec", "[i32]").unwrap().get::<P<Ty>>("a");
    assert_eq!(pprust::ty_to_string(&argument), "i32");
}

#[test]
fn test_parse_arguments_specific() {
    parse("foo + bar", "foo + bar").unwrap();
}

#[test]
fn test_parse_arguments_delimited() {
    parse("()", "()").unwrap();

    let argument = parse("($a:attr)", "(#[test])").unwrap().get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[test]");
    //assert_span_eq!(argument.span, 1, 8);

    let argument = parse("($a:attr_name_value)", "(#[foo=\"bar\"])").unwrap();
    let (name, value) = argument.get::<(String, Lit)>("a");
    assert_eq!(name, "foo");
    assert_eq!(pprust::lit_to_string(&value), "\"bar\"");

    parse("(foo + bar)", "(foo + bar)").unwrap();

    let arguments = parse("($($a:attr)?)", "(#[test])").unwrap();
    let arguments = arguments.get_sequence("a").into_option::<Attribute>().unwrap();
    assert_eq!(pprust::attribute_to_string(&arguments), "#[test]");
    //assert_span_eq!(arguments.span, 1, 8);

    assert_eq!(parse("($a:(foo)?)", "(foo)").unwrap().get::<Spanned<bool>>("a").node, true);
}

#[test]
fn test_parse_arguments_sequence() {
    parse("$()?", "").unwrap();
    parse("$()*", "").unwrap();
    parse("$()+", "").unwrap();

    let arguments = parse("$($a:attr)?", "").unwrap();
    let arguments = arguments.get_sequence("a").into_option::<Attribute>();
    assert_eq!(arguments, None);

    let arguments = parse("$($a:attr)?", "#[test]").unwrap();
    let arguments = arguments.get_sequence("a").into_option::<Attribute>().unwrap();
    assert_eq!(pprust::attribute_to_string(&arguments), "#[test]");
    //assert_span_eq!(arguments.span, 0, 7);

    let arguments = parse("$($a:attr)*", "").unwrap();
    let arguments = arguments.get_sequence("a").into_vec::<Attribute>();
    assert_eq!(arguments.len(), 0);

    let arguments = parse("$($a:attr)*", "#[test]").unwrap();
    let arguments = arguments.get_sequence("a").into_vec::<Attribute>();
    assert_eq!(arguments.len(), 1);
    assert_eq!(pprust::attribute_to_string(&arguments[0]), "#[test]");
    //assert_span_eq!(arguments[0].span, 0, 7);

    let arguments = parse("$($a:attr)*", "#[test] #[foo(bar, baz)]").unwrap();
    let arguments = arguments.get_sequence("a").into_vec::<Attribute>();
    assert_eq!(arguments.len(), 2);
    assert_eq!(pprust::attribute_to_string(&arguments[0]), "#[test]");
    //assert_span_eq!(arguments[0].span, 0, 7);
    //assert_span_eq!(arguments[1].span, 8, 24);

    let arguments = parse("$($a:attr)+", "#[test]").unwrap();
    let arguments = arguments.get_sequence("a").into_vec::<Attribute>();
    assert_eq!(arguments.len(), 1);
    assert_eq!(pprust::attribute_to_string(&arguments[0]), "#[test]");
    //assert_span_eq!(arguments[0].span, 0, 7);

    let arguments = parse("$($a:attr)+", "#[test] #[foo(bar, baz)]").unwrap();
    let arguments = arguments.get_sequence("a").into_vec::<Attribute>();
    assert_eq!(arguments.len(), 2);

    assert_eq!(pprust::attribute_to_string(&arguments[0]), "#[test]");
    //assert_span_eq!(arguments[0].span, 0, 7);

    assert_eq!(pprust::attribute_to_string(&arguments[1]), "#[foo(bar, baz)]");
    //assert_span_eq!(arguments[1].span, 8, 24);

    let specification = "$($a:{A($a:attr), B($b:binop)})+";
    let arguments = parse(specification, "#[test] + #[foo(bar, baz)] -").unwrap();
    let arguments = arguments.get_sequence("a").into_enum_vec(|e| e);
    assert_eq!(arguments.len(), 4);

    assert_eq!(arguments[0].variant, 0);
    let argument = arguments[0].arguments.get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[test]");
    //assert_span_eq!(argument.span, 0, 7);

    assert_eq!(arguments[1].variant, 1);
    let argument = arguments[1].arguments.get::<Spanned<BinOpToken>>("b");
    assert_eq!(argument.node, BinOpToken::Plus);
    assert_span_eq!(argument.span, 8, 9);

    assert_eq!(arguments[2].variant, 0);
    let argument = arguments[2].arguments.get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[foo(bar, baz)]");
    //assert_span_eq!(argument.span, 10, 26);

    assert_eq!(arguments[3].variant, 1);
    let argument = arguments[3].arguments.get::<Spanned<BinOpToken>>("b");
    assert_eq!(argument.node, BinOpToken::Minus);
    assert_span_eq!(argument.span, 27, 28);

    let arguments = parse("$($($a:attr), *), *", "#[test]").unwrap();
    let arguments = arguments.get_sequence("a").into_sequence_vec(|s| s.into_vec::<Attribute>());
    assert_eq!(arguments.len(), 1);
    assert_eq!(arguments[0].len(), 1);
    assert_eq!(pprust::attribute_to_string(&arguments[0][0]), "#[test]");
    //assert_span_eq!(arguments[0][0].span, 0, 7);
}

#[test]
fn test_parse_arguments_named_sequence() {
    assert_eq!(parse("$a:()?", "").unwrap().get::<Spanned<bool>>("a").node, false);
    assert_eq!(parse("$a:()*", "").unwrap().get::<Spanned<usize>>("a").node, 0);
    assert_eq!(parse("$a:()+", "").unwrap().get::<Spanned<usize>>("a").node, 0);

    assert_eq!(parse("$a:(foo)?", "foo").unwrap().get::<Spanned<bool>>("a").node, true);
    assert_eq!(parse("$a:(foo)*", "foo").unwrap().get::<Spanned<usize>>("a").node, 1);
    assert_eq!(parse("$a:(foo)*", "foo foo").unwrap().get::<Spanned<usize>>("a").node, 2);
    assert_eq!(parse("$a:(foo)+", "foo").unwrap().get::<Spanned<usize>>("a").node, 1);
    assert_eq!(parse("$a:(foo)+", "foo foo").unwrap().get::<Spanned<usize>>("a").node, 2);
}

#[test]
fn test_parse_arguments_enum() {
    let arguments = parse("$a:{A()}", "").unwrap();
    let arguments = arguments.get_enum("a");
    assert_eq!(arguments.variant, 0);

    let arguments = parse("$a:{A($a:attr), B($b:binop)}", "#[test]").unwrap();
    let arguments = arguments.get_enum("a");
    assert_eq!(arguments.variant, 0);
    let argument = arguments.arguments.get::<Attribute>("a");
    assert_eq!(pprust::attribute_to_string(&argument), "#[test]");
    //assert_span_eq!(argument.span, 0, 7);

    let arguments = parse("$a:{A($a:attr), B($b:binop)}", "+").unwrap();
    let arguments = arguments.get_enum("a");
    assert_eq!(arguments.variant, 1);
    let argument = arguments.arguments.get::<Spanned<BinOpToken>>("b");
    assert_eq!(argument.node, BinOpToken::Plus);
    assert_span_eq!(argument.span, 0, 1);
}
