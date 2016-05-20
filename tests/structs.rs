use easy_plugin::{PluginResult};

use syntax::codemap::{Span};
use syntax::ext::base::{DummyResult, ExtCtxt, MacResult};

easy_plugin! {
    struct Arguments { [$($a:ident $($b:ident)*), +] }

    pub fn expand_struct(
        context: &mut ExtCtxt, span: Span, arguments: Arguments
    ) -> PluginResult<Box<MacResult>> {
        assert_eq!(arguments.a.iter().map(|a| a.node).collect::<Vec<_>>(), &[
            context.ident_of("a"),
            context.ident_of("b"),
            context.ident_of("d"),
        ]);
        assert_eq!(arguments.b.iter().map(|b| {
            b.iter().map(|b| b.node).collect()
        }).collect::<Vec<Vec<_>>>(), &[
            vec![],
            vec![context.ident_of("c")],
            vec![context.ident_of("e"), context.ident_of("f")],
        ]);
        Ok(DummyResult::any(span))
    }
}

#[test]
fn test_easy_plugin_struct() {
    super::with_tts("[a, b c, d e f]", |c, s, a| {
        expand_struct(c, s, a);
    });
}
