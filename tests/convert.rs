#![feature(plugin, rustc_private)]
#![plugin(easy_plugin)]

#[allow(plugin_as_library)]
#[macro_use]
extern crate easy_plugin;

extern crate syntax;

use easy_plugin::{PluginResult};
use easy_plugin::convert::*;

use syntax::ast::{TokenTree};
use syntax::codemap::{Span, DUMMY_SP};
use syntax::ext::base::{ExtCtxt, DummyResult, MacResult};
use syntax::ext::expand::{ExpansionConfig};
use syntax::ext::quote::rt::{ExtParseUtils};
use syntax::parse::{ParseSess};

easy_plugin! {
    struct Arguments {
        $attr_list:attr
        $expr_vec:expr
        $item_fn:item
        $lit_str:lit
        $meta_list:meta
        $pat_ident:pat
        $stmt_decl:stmt;
        $ty_vec:ty
        $tok_bin_op:tok
        $tt_delimited:tt
    }

    pub fn expand_convert(
        _: &mut ExtCtxt, span: Span, arguments: Arguments
    ) -> PluginResult<Box<MacResult>> {
        attr_to_list(&arguments.attr_list).unwrap();
        expr_to_vec(&arguments.expr_vec).unwrap();
        item_to_fn(&arguments.item_fn).unwrap();
        lit_to_str(&arguments.lit_str).unwrap();
        meta_to_list(&arguments.meta_list).unwrap();
        pat_to_ident(&arguments.pat_ident).unwrap();
        stmt_to_decl(&arguments.stmt_decl).unwrap();
        ty_to_vec(&arguments.ty_vec).unwrap();
        tok_to_bin_op(&arguments.tok_bin_op).unwrap();
        tt_to_delimited(&arguments.tt_delimited).unwrap();
        Ok(DummyResult::any(span))
    }
}

#[test]
fn test_convert() {
    fn with_tts<F>(source: &str, f: F) where F: Fn(&mut ExtCtxt, Span, &[TokenTree]) {
        let session = ParseSess::new();
        let config = ExpansionConfig::default("".into());
        let mut cfgs = vec![];
        let mut context = ExtCtxt::new(&session, vec![], config, &mut cfgs);
        let tts = context.parse_tts(source.into());
        f(&mut context, DUMMY_SP, &tts);
    }

    let arguments = r#"
        #[cfg(target_os="windows")]
        [1, 2, 3]
        fn add(a: i32, b: i32) -> i32 { a + b }
        "string"
        cfg(target_os="windows")
        a
        let b = 322;
        [i32]
        +
        (1, 2, 3)
    "#;

    with_tts(arguments, |c, s, a| {
        expand_convert(c, s, a);
    });
}
