easy-plugin
===========

[![crates.io](  https://img.shields.io/crates/v/easy-plugin.svg)](https://crates.io/crates/easy-plugin)
[![Travis CI](https://travis-ci.org/KyleMayes/easy-plugin.svg?branch=master)](https://travis-ci.org/KyleMayes/easy-plugin)

A compiler plugin that makes it easier to write compiler plugins.

Released under the Apache License 2.0.

## Supported Configurations

* Nightly Rust channel
  ([Documentation](https://kylemayes.github.io/easy-plugin/nightly/easy_plugin))
* Stable and beta Rust channels
  ([Documentation](https://kylemayes.github.io/easy-plugin/stable/easy_plugin))

By default, `easy-plugin` expects to be compiled by a nightly Rust compiler. `easy-plugin` is also
supported on the stable and beta channels of Rust with
[`syntex`](https://github.com/serde-rs/syntex). To enable this support, enable the `stable` Cargo
feature.

### Example

```rust
easy_plugin! {
    struct Arguments {
		// An argument specification that accepts a simple binary expression.
    	$a:ident $operator:binop $b:ident
    }

    // The `arguments: Arguments` argument contains the parsed results of the
    // plugin arguments according to the above specification. An error is reported
    // if the plugin arguments cannot be parsed.
    pub fn expand_plugin(
        context: &mut ExtCtxt, span: Span, arguments: Arguments
    ) -> PluginResult<Box<MacResult>> {
    	// Accesses the parsed results.
        println!("{:?} {:?} {:?}", arguments.a, arguments.operator, arguments.b);

        // Returns `Ok` to signal this plugin completed successfully. An error is
        // reported if `Err` is returned instead.
        Ok(DummyResult::any(span))
    }
}

#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("plugin", expand_plugin);
}
```
