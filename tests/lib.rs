#![feature(plugin, plugin_registrar, rustc_private)]
#![plugin(easy_plugin)]

#[allow(plugin_as_library)]
extern crate easy_plugin;

extern crate rustc;
extern crate syntax;

use easy_plugin::{PluginResult, Specifier};

use rustc::plugin::{Registry};

use syntax::parse::token;
use syntax::ast::{KleeneOp, TokenTree};
use syntax::codemap::{Span, DUMMY_SP};
use syntax::ext::base::{ExtCtxt, DummyResult, MacResult};
use syntax::ext::expand::{ExpansionConfig};
use syntax::ext::quote::rt::{ExtParseUtils};
use syntax::parse::{ParseSess};
use syntax::parse::token::{BinOpToken, DelimToken, Lit, Token};

#[test]
fn test_parse_specification() {
    let specification: &[Specifier] = parse_specification!();
    assert_eq!(specification, &[]);

    let specification: &[Specifier] = parse_specification!(
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
    );

    let lit = Token::Literal(Lit::Integer(token::intern("322")), Some(token::intern("u32")));

    assert_eq!(specification, &[
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

easy_plugin! {
    struct Arguments { }

    pub fn expand_struct_none(
        _: &mut ExtCtxt, span: Span, _: Arguments
    ) -> PluginResult<Box<MacResult>> {
        Ok(DummyResult::any(span))
    }
}

easy_plugin! {
    struct Arguments {
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
        [$a:ident $b:ident]
        $($c:ident $($d:ident)*), +
    }

    pub fn expand_struct_all(
        _: &mut ExtCtxt, span: Span, arguments: Arguments
    ) -> PluginResult<Box<MacResult>> {
        macro_rules! check {
            ($print:ident, $actual:expr, $expected:expr) => ({
                assert_eq!(::syntax::print::pprust::$print(&$actual), $expected);
            });
        }

        check!(attribute_to_string, arguments.attr, r#"#[cfg(target_os = "windows")]"#);
        assert_eq!(arguments.binop, BinOpToken::Plus);
        check!(block_to_string, arguments.block, "{ let a = 322; a }");
        assert_eq!(arguments.delim.delim, DelimToken::Bracket);
        check!(tts_to_string, arguments.delim.tts, "1 , 2 , 3");
        check!(expr_to_string, arguments.expr, "2 + 2");
        assert_eq!(&*arguments.ident.name.as_str(), "foo");
        check!(item_to_string, arguments.item, "struct Bar;");
        assert_eq!(&*arguments.lftm.as_str(), "'baz");
        check!(lit_to_string, arguments.lit, "322");
        check!(meta_item_to_string, arguments.meta, r#"cfg(target_os = "windows")"#);
        check!(pat_to_string, arguments.pat, r#"(foo, "bar")"#);
        check!(path_to_string, arguments.path, "::std::vec::Vec<i32>");
        check!(stmt_to_string, arguments.stmt, "let a = 322;");
        check!(ty_to_string, arguments.ty, "i32");
        check!(token_to_string, arguments.tok, "~");
        check!(tt_to_string, arguments.tt, "!");
        assert_eq!(&*arguments.a.name.as_str(), "a");
        assert_eq!(&*arguments.b.name.as_str(), "b");

        assert_eq!(arguments.c.len(), 3);
        assert_eq!(&*arguments.c[0].name.as_str(), "a");
        assert_eq!(&*arguments.c[1].name.as_str(), "b");
        assert_eq!(&*arguments.c[2].name.as_str(), "d");

        assert_eq!(arguments.d.len(), 3);

        assert_eq!(arguments.d[0].len(), 0);

        assert_eq!(arguments.d[1].len(), 1);
        assert_eq!(&*arguments.d[1][0].name.as_str(), "c");

        assert_eq!(arguments.d[2].len(), 2);
        assert_eq!(&*arguments.d[2][0].name.as_str(), "e");
        assert_eq!(&*arguments.d[2][1].name.as_str(), "f");

        Ok(DummyResult::any(span))
    }
}

easy_plugin! {
    enum Arguments {
        A { },
        B { [$a:ident $b:ident] },
        C { $($a:ident $($b:ident)*), + },
    }

    pub fn expand_enum(
        _: &mut ExtCtxt, span: Span, arguments: Arguments
    ) -> PluginResult<Box<MacResult>> {
        match arguments {
            Arguments::A(_) => { },
            Arguments::B(b) => {
                assert_eq!(&*b.a.name.as_str(), "a");
                assert_eq!(&*b.b.name.as_str(), "b");
            },
            Arguments::C(c) => {
                assert_eq!(c.a.len(), 3);
                assert_eq!(&*c.a[0].name.as_str(), "a");
                assert_eq!(&*c.a[1].name.as_str(), "b");
                assert_eq!(&*c.a[2].name.as_str(), "d");

                assert_eq!(c.b.len(), 3);

                assert_eq!(c.b[0].len(), 0);

                assert_eq!(c.b[1].len(), 1);
                assert_eq!(&*c.b[1][0].name.as_str(), "c");

                assert_eq!(c.b[2].len(), 2);
                assert_eq!(&*c.b[2][0].name.as_str(), "e");
                assert_eq!(&*c.b[2][1].name.as_str(), "f");
            },
        }

        Ok(DummyResult::any(span))
    }
}

#[test]
fn test_easy_plugin() {
    fn with_tts<F>(source: &str, f: F) where F: Fn(&mut ExtCtxt, Span, &[TokenTree]) {
        let session = ParseSess::new();
        let config = ExpansionConfig::default("".into());
        let mut cfgs = vec![];
        let mut context = ExtCtxt::new(&session, vec![], config, &mut cfgs);
        let tts = context.parse_tts(source.into());
        f(&mut context, DUMMY_SP, &tts);
    }

    with_tts("", |c, s, a| {
        expand_struct_none(c, s, a);
    });

    let arguments = r#"
        #[cfg(target_os = "windows")]
        +
        { let a = 322; a }
        [1, 2, 3]
        2 + 2
        foo
        struct Bar;
        'baz
        322
        cfg(target_os="windows")
        (foo, "bar")
        ::std::vec::Vec<i32>
        let a = 322
        i32
        ~
        !
        [a b]
        a, b c, d e f
    "#;

    with_tts(arguments, |c, s, a| {
        expand_struct_all(c, s, a);
    });

    with_tts("", |c, s, a| {
        expand_enum(c, s, a);
    });

    with_tts("[a b]", |c, s, a| {
        expand_enum(c, s, a);
    });

    with_tts("a, b c, d e f", |c, s, a| {
        expand_enum(c, s, a);
    });
}

#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("struct_none", expand_struct_none);
    registry.register_macro("struct_all", expand_struct_all);
    //registry.register_macro("enum", expand_enum);
}
