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
use syntax::ext::base::{ExtCtxt};
use syntax::ext::expand::{ExpansionConfig};
use syntax::ext::quote::rt::{ExtParseUtils};
use syntax::parse::{ParseSess};

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
    let mut cfgs = vec![];
    let mut context = ExtCtxt::new(&session, vec![], config, &mut cfgs);
    let tts = context.parse_tts(source.into());
    f(&mut context, DUMMY_SP, &tts);
}

#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("enum", enums::expand_enum);
    registry.register_macro("struct_none", structs::expand_struct_none);
    registry.register_macro("struct_all", structs::expand_struct_all);
}
