#![feature(plugin, plugin_registrar, rustc_private)]
#![plugin(easy_plugin)]

#[allow(plugin_as_library)]
#[macro_use]
extern crate easy_plugin;

extern crate rustc_plugin;
extern crate syntax;

use rustc_plugin::{Registry};

use syntax::ast::{TokenTree};
use syntax::codemap::{Span, DUMMY_SP};
use syntax::ext::base::{DummyMacroLoader, ExtCtxt};
use syntax::ext::expand::{ExpansionConfig};
use syntax::ext::quote::rt::{ExtParseUtils};
use syntax::parse::{ParseSess};

// check! ________________________________________

macro_rules! check {
    ($print:ident, $actual:expr, $expected:expr) => ({
        assert_eq!(::syntax::print::pprust::$print(&$actual), $expected);
    });
}

// assert_span_eq! _______________________________

macro_rules! assert_span_eq {
    ($context:expr, $span:expr, $sl:expr, $sc:expr, $el:expr, $ec:expr) => ({
        let start = $context.codemap().lookup_char_pos($span.lo);
        assert_eq!((start.line, start.col.0), ($sl, $sc));
        let end = $context.codemap().lookup_char_pos($span.hi);
        assert_eq!((end.line, end.col.0), ($el, $ec));
    });
}

mod arguments;
mod convert;
mod enums;
mod specification;
mod structs;

//================================================
// Functions
//================================================

fn with_tts<F>(source: &str, f: F) where F: Fn(&mut ExtCtxt, Span, &[TokenTree]) {
    let session = ParseSess::new();
    let config = ExpansionConfig::default("".into());
    let mut loader = DummyMacroLoader;
    let mut context = ExtCtxt::new(&session, vec![], config, &mut loader);
    let tts = context.parse_tts(source.into());
    f(&mut context, DUMMY_SP, &tts);
}

#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("enum", enums::expand_enum);
    registry.register_macro("struct", structs::expand_struct);
}
