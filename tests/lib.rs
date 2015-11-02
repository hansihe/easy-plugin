#![allow(plugin_as_library)]
#![feature(plugin, rustc_private)]

#![plugin(easy_plugin)]

extern crate easy_plugin;
extern crate syntax;

use easy_plugin::{Specifier};

use syntax::parse::token;
use syntax::ast::{KleeneOp};
use syntax::parse::token::{BinOpToken, DelimToken, Lit, Token};

#[test]
fn test_parse_specification() {
    let specification: &[Specifier] = parse_specification!();
    assert_eq!(specification, &[]);

    let specification: &[Specifier] = parse_specification!(
        $binop:binop
        $block:block
        $delim:delim
        $expr:expr
        $ident:ident
        $item:item
        $lftm:lftm
        $lit:lit
        $meta:meta
        $pat:pat
        $path:path
        $stmt:stmt
        $ty:ty
        $tok:tok
        $tt:tt
        +
        322u32
        foo
        'bar
        /// comment
        [$a:ident $b:ident]
        $($c:ident $($d:ident)*), +
    );

    let lit = Token::Literal(Lit::Integer(token::intern("322")), Some(token::intern("u32")));

    assert_eq!(specification, &[
        Specifier::BinOp("binop".into()),
        Specifier::Block("block".into()),
        Specifier::Delim("delim".into()),
        Specifier::Expr("expr".into()),
        Specifier::Ident("ident".into()),
        Specifier::Item("item".into()),
        Specifier::Lftm("lftm".into()),
        Specifier::Lit("lit".into()),
        Specifier::Meta("meta".into()),
        Specifier::Pat("pat".into()),
        Specifier::Path("path".into()),
        Specifier::Stmt("stmt".into()),
        Specifier::Ty("ty".into()),
        Specifier::Tok("tok".into()),
        Specifier::Tt("tt".into()),
        Specifier::Specific(Token::BinOp(BinOpToken::Plus)),
        Specifier::Specific(lit),
        Specifier::specific_ident("foo"),
        Specifier::specific_lftm("'bar"),
        Specifier::Specific(Token::DocComment(token::intern("/// comment"))),
        Specifier::Delimited(DelimToken::Bracket, vec![
            Specifier::Ident("a".into()),
            Specifier::Ident("b".into()),
        ]),
        Specifier::Sequence(KleeneOp::OneOrMore, Some(Token::Comma), vec![
            Specifier::Ident("c".into()),
            Specifier::Sequence(KleeneOp::ZeroOrMore, None, vec![
                Specifier::Ident("d".into()),
            ]),
        ]),
    ]);
}
