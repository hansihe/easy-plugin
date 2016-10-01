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

The following usage of `easy_plugin!` defines a plugin which accepts key-value pairs.

```rust
easy_plugin! {
    // A key can either be an identifier or a string literal.
    enum Key {
        Ident { $key:ident },
        Lit { $key:lit_str },
    }

    // A key-value pair is a key followed by `=>` and any expression.
    struct KeyValuePair {
        $key:$Key => $value:expr
    }

    // This plugin accepts one or more comma-separated key-value pairs.
    struct Arguments {
        $($kvp:$KeyValuePair), + $(,)?
    }

    pub fn expand_kvp(
        _: &mut ExtCtxt, span: Span, arguments: Arguments
    ) -> PluginResult<Box<MacResult>> {
        for KeyValuePair { key, value } in arguments.kvp {
            match key {
                Key::Ident { key } => println!("Key:   {}", key.node),
                Key::Lit { key } => println!("Key:   {:?}", key.0),
            }
            println!("Value: {}", pprust::expr_to_string(&value));
        }
        Ok(DummyResult::any(span))
    }
}

#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("kvp", expand_kvp);
}
```
