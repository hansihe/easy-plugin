#![allow(unused)]
#![feature(plugin, plugin_registrar, rustc_private)]
#![plugin(easy_plugin)]

#[allow(plugin_as_library)]
extern crate easy_plugin;

use easy_plugin::{PluginResult};

extern crate rustc_plugin;
extern crate syntax;

use rustc_plugin::{Registry};

use syntax::codemap::{Span};
use syntax::ext::base::{ExtCtxt, DummyResult, MacResult};

easy_plugin! {
    enum Arguments {
    	A { },
    	B { $a:ident },
    }

    /// My plugin.
    pub fn expand_plugin(
        context: &mut ExtCtxt, span: Span, arguments: Arguments
    ) -> PluginResult<Box<MacResult>> {
    	match arguments {
    		Arguments::A(a) => { },
    		Arguments::B(b) => println!("{:?}", b.a),
    	}

        Ok(DummyResult::any(span))
    }
}

#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("plugin", expand_plugin);
}

fn main() { }

// This example is explained in the crate-level documentation.
