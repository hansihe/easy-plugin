use easy_plugin::{PluginResult};

use syntax::codemap::{Span};
use syntax::ext::base::{DummyResult, ExtCtxt, MacResult};
use syntax::parse::token::{BinOpToken, DelimToken};

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
        $($c:ident $($d:ident)*), +;
        $($e:ident)?; $($f:ident)?;
        $($($g:ident)? $($h:ident)?), +;
        $kappa:(Kappa), +;
        $($keepo:(Keepo)?), +;
    }

    pub fn expand_struct_all(
        context: &mut ExtCtxt, span: Span, arguments: Arguments
    ) -> PluginResult<Box<MacResult>> {
        macro_rules! assert_span_eq {
            ($span:expr, $sl:expr, $sc:expr, $el:expr, $ec:expr) => ({
                let start = context.codemap().lookup_char_pos($span.lo);
                assert_eq!((start.line, start.col.0), ($sl, $sc));
                let end = context.codemap().lookup_char_pos($span.hi);
                assert_eq!((end.line, end.col.0), ($el, $ec));
            });
        }

        assert_span_eq!(arguments.attr.span, 2, 8, 2, 35);
        assert_span_eq!(arguments.binop.span, 3, 8, 3, 9);
        assert_span_eq!(arguments.block.span, 4, 8, 4, 26);
        assert_span_eq!(arguments.delim.span, 5, 8, 5, 17);
        assert_span_eq!(arguments.expr.span, 6, 8, 6, 13);
        assert_span_eq!(arguments.ident.span, 7, 8, 7, 11);
        assert_span_eq!(arguments.item.span, 8, 8, 8, 19);
        assert_span_eq!(arguments.lftm.span, 9, 8, 9, 12);
        assert_span_eq!(arguments.lit.span, 10, 8, 10, 11);
        assert_span_eq!(arguments.meta.span, 11, 8, 11, 32);
        assert_span_eq!(arguments.pat.span, 12, 8, 12, 20);
        assert_span_eq!(arguments.path.span, 13, 8, 13, 28);
        assert_span_eq!(arguments.stmt.span, 14, 8, 14, 19);
        assert_span_eq!(arguments.ty.span, 15, 8, 15, 11);
        assert_span_eq!(arguments.tok.span, 16, 8, 16, 9);
        assert_span_eq!(arguments.tt.get_span(), 17, 8, 17, 9);

        macro_rules! check {
            ($print:ident, $actual:expr, $expected:expr) => ({
                assert_eq!(::syntax::print::pprust::$print(&$actual), $expected);
            });
        }

        check!(attribute_to_string, arguments.attr, r#"#[cfg(target_os = "windows")]"#);
        assert_eq!(arguments.binop.node, BinOpToken::Plus);
        check!(block_to_string, arguments.block, "{ let a = 322; a }");
        assert_eq!(arguments.delim.node.delim, DelimToken::Bracket);
        check!(tts_to_string, arguments.delim.node.tts, "1 , 2 , 3");
        check!(expr_to_string, arguments.expr, "2 + 2");
        assert_eq!(arguments.ident.node, context.ident_of("foo"));
        check!(item_to_string, arguments.item, "struct Bar;");
        assert_eq!(arguments.lftm.node, context.name_of("'baz"));
        check!(lit_to_string, arguments.lit, "322");
        check!(meta_item_to_string, arguments.meta, r#"cfg(target_os = "windows")"#);
        check!(pat_to_string, arguments.pat, r#"(foo, "bar")"#);
        check!(path_to_string, arguments.path, "::std::vec::Vec<i32>");
        check!(stmt_to_string, arguments.stmt, "let a = 322;");
        check!(ty_to_string, arguments.ty, "i32");
        check!(token_to_string, arguments.tok.node, "~");
        check!(tt_to_string, arguments.tt, "!");
        assert_eq!(arguments.a.node, context.ident_of("a"));
        assert_eq!(arguments.b.node, context.ident_of("b"));
        assert_eq!(arguments.c.iter().map(|c| c.node).collect::<Vec<_>>(), &[
            context.ident_of("a"),
            context.ident_of("b"),
            context.ident_of("d"),
        ]);
        assert_eq!(arguments.d.iter().map(|d| {
            d.iter().map(|d| d.node).collect()
        }).collect::<Vec<Vec<_>>>(), &[
            vec![],
            vec![context.ident_of("c")],
            vec![context.ident_of("e"), context.ident_of("f")],
        ]);
        assert_eq!(arguments.e, None);
        assert_eq!(arguments.f.map(|f| f.node), Some(context.ident_of("g")));
        assert_eq!(arguments.g.iter().map(|g| g.map(|g| g.node)).collect::<Vec<_>>(), vec![
            None,
            Some(context.ident_of("h")),
            Some(context.ident_of("i")),
        ]);
        assert_eq!(arguments.h.iter().map(|h| h.map(|h| h.node)).collect::<Vec<_>>(), vec![
            None,
            None,
            Some(context.ident_of("j")),
        ]);
        assert_eq!(arguments.kappa.node, 3);
        assert_eq!(arguments.keepo.iter().map(|k| k.node).collect::<Vec<_>>(), &[
            false, true, false, true
        ]);
        Ok(DummyResult::any(span))
    }
}

#[test]
fn test_easy_plugin_struct() {
    super::with_tts("", |c, s, a| {
        expand_struct_none(c, s, a);
    });

    let arguments = r#"
        #[cfg(target_os="windows")]
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
        a, b c, d e f;
        ;
        g;
        , h, i j;
        Kappa, Kappa, Kappa;
        , Keepo, , Keepo;
    "#;

    super::with_tts(arguments, |c, s, a| {
        expand_struct_all(c, s, a);
    });
}
