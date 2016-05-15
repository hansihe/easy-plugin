use easy_plugin::{PluginResult};
use easy_plugin::convert::*;

use syntax::codemap::{Span};
use syntax::ext::base::{DummyResult, ExtCtxt, MacResult};

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

    super::with_tts(arguments, |c, s, a| {
        expand_convert(c, s, a);
    });
}
