use easy_plugin::{PluginResult};

use syntax::codemap::{Span};
use syntax::ext::base::{DummyResult, ExtCtxt, MacResult};

easy_plugin! {
    enum Arguments {
        A { },
        B { [$a:ident $b:ident] },
        C { $($a:ident $($b:ident)*), + },
    }

    pub fn expand_enum(
        context: &mut ExtCtxt, span: Span, arguments: Arguments
    ) -> PluginResult<Box<MacResult>> {
        match arguments {
            Arguments::A(_) => { },
            Arguments::B(b) => {
                assert_eq!(b.a.node, context.ident_of("a"));
                assert_eq!(b.b.node, context.ident_of("b"));
            },
            Arguments::C(c) => {
                assert_eq!(c.a.iter().map(|a| a.node).collect::<Vec<_>>(), &[
                    context.ident_of("a"),
                    context.ident_of("b"),
                    context.ident_of("d"),
                ]);
                assert_eq!(c.b.iter().map(|b| {
                    b.iter().map(|b| b.node).collect()
                }).collect::<Vec<Vec<_>>>(), &[
                    vec![],
                    vec![context.ident_of("c")],
                    vec![context.ident_of("e"), context.ident_of("f")],
                ]);
            },
        }
        Ok(DummyResult::any(span))
    }
}

#[test]
fn test_easy_plugin_enum() {
    super::with_tts("", |c, s, a| {
        expand_enum(c, s, a);
    });

    super::with_tts("[a b]", |c, s, a| {
        expand_enum(c, s, a);
    });

    super::with_tts("a, b c, d e f", |c, s, a| {
        expand_enum(c, s, a);
    });
}
