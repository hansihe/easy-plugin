#![feature(plugin, rustc_private)]
#![plugin(easy_plugin)]

#[allow(plugin_as_library)]
#[macro_use]
extern crate easy_plugin;

extern crate syntax;

use easy_plugin::{Amount, Specification, Specifier};

use syntax::parse::token;
use syntax::parse::token::{BinOpToken, DelimToken, Lit, Token};

#[test]
fn test_parse_specification() {
    let specification: Specification = parse_specification!();
    assert_eq!(specification, spec![]);

    let specification: Specification = parse_specification!(
        $attr:attr
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
        $($e:ident)?
        $kappa:(Kappa)*
        $keepo:(Keepo), +
    );
    assert_eq!(specification, spec![
        Specifier::Attr("attr".into()),
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
        Specifier::Specific(
            Token::Literal(Lit::Integer(token::intern("322")), Some(token::intern("u32")))
        ),
        Specifier::specific_ident("foo"),
        Specifier::specific_lftm("'bar"),
        Specifier::Specific(Token::DocComment(token::intern("/// comment"))),
        Specifier::Delimited(DelimToken::Bracket, spec![
            Specifier::Ident("a".into()),
            Specifier::Ident("b".into()),
        ]),
        Specifier::Sequence(Amount::OneOrMore, Some(Token::Comma), spec![
            Specifier::Ident("c".into()),
            Specifier::Sequence(Amount::ZeroOrMore, None, spec![
                Specifier::Ident("d".into()),
            ]),
        ]),
        Specifier::Sequence(Amount::ZeroOrOne, None, spec![
            Specifier::Ident("e".into()),
        ]),
        Specifier::NamedSequence("kappa".into(), Amount::ZeroOrMore, None, spec![
            Specifier::specific_ident("Kappa"),
        ]),
        Specifier::NamedSequence("keepo".into(), Amount::OneOrMore, Some(Token::Comma), spec![
            Specifier::specific_ident("Keepo"),
        ]),
    ]);
}
