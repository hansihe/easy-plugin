#![cfg_attr(not(feature="syntex"), feature(plugin))]
#![cfg_attr(not(feature="syntex"), feature(plugin_registrar))]
#![cfg_attr(not(feature="syntex"), feature(rustc_private))]

#![cfg_attr(not(feature="syntex"), plugin(easy_plugin))]

#[cfg(feature="syntex")]
extern crate syntex as rustc_plugin;
#[cfg(feature="syntex")]
extern crate syntex_syntax as syntax;

#[cfg(not(feature="syntex"))]
extern crate rustc_plugin;
#[cfg(not(feature="syntex"))]
extern crate syntax;

#[cfg_attr(not(feature="syntex"), allow(plugin_as_library))]
#[macro_use]
extern crate easy_plugin;

use syntax::codemap::{Span, DUMMY_SP};
use syntax::ext::base::{DummyMacroLoader, ExtCtxt};
use syntax::ext::expand::{ExpansionConfig};
use syntax::ext::quote::rt::{ExtParseUtils};
use syntax::parse::{ParseSess};
use syntax::tokenstream::{TokenTree};

//================================================
// Macros
//================================================

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

mod arguments { include!(concat!(env!("OUT_DIR"), "/arguments.rs")); }
mod convert { include!(concat!(env!("OUT_DIR"), "/convert.rs")); }
mod enums { include!(concat!(env!("OUT_DIR"), "/enums.rs")); }
mod errors { include!(concat!(env!("OUT_DIR"), "/errors.rs")); }
mod specification { include!(concat!(env!("OUT_DIR"), "/specification.rs")); }
mod structs { include!(concat!(env!("OUT_DIR"), "/structs.rs")); }
