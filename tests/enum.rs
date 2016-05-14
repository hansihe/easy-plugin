#![feature(plugin, plugin_registrar, rustc_private)]
#![plugin(easy_plugin)]

#[allow(plugin_as_library)]
#[macro_use]
extern crate easy_plugin;

extern crate rustc_plugin;
extern crate syntax;

use easy_plugin::{PluginResult};

use rustc_plugin::{Registry};

use syntax::ast::{TokenTree};
use syntax::codemap::{Span, DUMMY_SP};
use syntax::ext::base::{ExtCtxt, DummyResult, MacResult};
use syntax::ext::expand::{ExpansionConfig};
use syntax::ext::quote::rt::{ExtParseUtils};
use syntax::parse::{ParseSess};

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
    fn with_tts<F>(source: &str, f: F) where F: Fn(&mut ExtCtxt, Span, &[TokenTree]) {
        let session = ParseSess::new();
        let config = ExpansionConfig::default("".into());
        let mut cfgs = vec![];
        let mut context = ExtCtxt::new(&session, vec![], config, &mut cfgs);
        let tts = context.parse_tts(source.into());
        f(&mut context, DUMMY_SP, &tts);
    }

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
    registry.register_macro("enum", expand_enum);
}
