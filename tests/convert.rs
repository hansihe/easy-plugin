use easy_plugin::{PluginResult};
use easy_plugin::convert::*;

use syntax::codemap::{Span};
use syntax::ext::base::{DummyResult, ExtCtxt, MacResult};

easy_plugin! {
    struct Arguments {
        $attr_list:attr
        $expr_addr_of:expr
        $item_const:item
        $lit_bool:lit
        $meta_list:meta
        $pat_ident:pat
        $stmt_decl:stmt;
        $ty_bare_fn:ty
        $tok_bin_op:tok
        $tt_delimited:tt
    }

    pub fn expand_convert(
        _: &mut ExtCtxt, span: Span, arguments: Arguments
    ) -> PluginResult<Box<MacResult>> {
        attr_to_list(&arguments.attr_list).unwrap();
        expr_to_addr_of(&arguments.expr_addr_of).unwrap();
        item_to_const(&arguments.item_const).unwrap();
        lit_to_bool(&arguments.lit_bool).unwrap();
        meta_to_list(&arguments.meta_list).unwrap();
        pat_to_ident(&arguments.pat_ident).unwrap();
        stmt_to_decl(&arguments.stmt_decl).unwrap();
        ty_to_bare_fn(&arguments.ty_bare_fn).unwrap();
        tok_to_bin_op(&arguments.tok_bin_op).unwrap();
        tt_to_delimited(&arguments.tt_delimited).unwrap();
        Ok(DummyResult::any(span))
    }
}

#[test]
fn test_convert() {
    let arguments = r#"
        #[cfg(target_os="windows")]
        &foo
        const BAR: i32 = 322;
        true
        cfg(target_os="windows")
        baz
        let b = 322;
        fn(i32, i32) -> i32
        +
        (1, 2, 3)
    "#;

    super::with_tts(arguments, |c, s, a| {
        expand_convert(c, s, a);
    });
}
