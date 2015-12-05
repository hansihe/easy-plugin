//! This crate provides a compiler plugin, `easy_plugin!`, which makes it easier to write compiler
//! plugins.
//!
//! `easy_plugin!` generates a wrapper function around your plugin function which handles argument
//! parsing and error reporting for you, significantly reducing the time it takes to write a plugin.
//! It can be used one of two ways, one which allows for only one argument specification and another
//! that allows for multiple argument specifications.
//!
//! First, here is a trivial
//! [example](https://github.com/KyleMayes/easy-plugin/blob/master/examples/struct.rs) of the first
//! form that only allows for one argument specification.
//!
//! ```ignore
//! #![feature(plugin, plugin_registrar, rustc_private)]
//! #![plugin(easy_plugin)]
//!
//! #[allow(plugin_as_library)]
//! extern crate easy_plugin;
//!
//! use easy_plugin::{PluginResult};
//!
//! // rustc_plugin and syntax imports...
//!
//! easy_plugin! {
//!     struct Arguments { $a:ident }
//!
//!     /// My plugin.
//!     pub fn expand_plugin(
//!         context: &mut ExtCtxt, span: Span, arguments: Arguments
//!     ) -> PluginResult<Box<MacResult>> {
//!         println!("{:?}", arguments.a);
//!         Ok(DummyResult::any(span))
//!     }
//! }
//!
//! #[plugin_registrar]
//! pub fn plugin_registrar(registry: &mut Registry) {
//!     registry.register_macro("plugin", expand_plugin);
//! }
//! ```
//!
//! In this example, note that the arguments of the plugin function `expand_plugin` differ from a
//! typical plugin function in that the last argument is of type `Arguments` rather than
//! `&[TokenTree]`. This is because the generated wrapper function handles argument parsing for you.
//! The faux-definition of `Arguments` above `expand_plugin` provides the argument specification and
//! the generated wrapper function parses the arguments and stores them in an instance of
//! `Arguments`.
//!
//! In this example, the argument specification consists of `$a:ident`, which means that the only
//! argument this plugin will accept is a single identifier which will be stored in a field named
//! `a` in the `Arguments` struct. For more information on argument specifications, see the relevant
//! section [below](#specifications).
//!
//! If the arguments do not match the argument specification or your plugin function returns `Err`,
//! the wrapper function will report an error with `ExtCtxt::span_err` for you.
//!
//! Note that the `expand_plugin` function is public and has a documentation comment. The visibility
//! and attributes applied to your plugin function (including documentation comments) will be
//! applied to the wrapper function. In this example, the wrapper function will be public and have
//! a documentation comment.
//!
//! Next, here is a trivial
//! [example](https://github.com/KyleMayes/easy-plugin/blob/master/examples/enum.rs) of the second
//! form that allows for multiple argument specifications.
//!
//! ```ignore
//! #![feature(plugin, plugin_registrar, rustc_private)]
//! #![plugin(easy_plugin)]
//!
//! #[allow(plugin_as_library)]
//! extern crate easy_plugin;
//!
//! use easy_plugin::{PluginResult};
//!
//! // rustc_plugin and syntax imports...
//!
//! easy_plugin! {
//!     enum Arguments {
//!         A { },
//!         B { $a:ident }, // <- this trailing comma is required!
//!     }
//!
//!     /// My plugin.
//!     pub fn expand_plugin(
//!         context: &mut ExtCtxt, span: Span, arguments: Arguments
//!     ) -> PluginResult<Box<MacResult>> {
//!         match arguments {
//!             Arguments::A(a) => { },
//!             Arguments::B(b) => println!("{:?}", b.a),
//!         }
//!
//!         Ok(DummyResult::any(span))
//!     }
//! }
//!
//! #[plugin_registrar]
//! pub fn plugin_registrar(registry: &mut Registry) {
//!     registry.register_macro("plugin", expand_plugin);
//! }
//! ```
//!
//! This form behaves much like the first, except that a parse of the arguments will be attempted
//! with each specification in the provided order until one succeeds. If every attempt fails, the
//! resulting error message will be from the final parse attempt. The results of a successful parse
//! will be stored in a struct which will then be stored in an enum variant of the same name.
//!
//! In this example, if the arguments consist of a single identifier, the first parse attempt will
//! fail but the second will succeed. The identifier will be stored in a field named `a` in a struct
//! named `B`. This struct will then be stored in the enum variant `Arguments::B`.
//!
//! # Specifications
//!
//! Plugin argument specifications are very similar to the argument specifications you are used to
//! writing for macros. There are two primary differences: no restrictions on ordering and
//! additional types of named specifiers.
//!
//! | Name    | Description                           |  Storage Type                           |
//! |:--------|:--------------------------------------|:----------------------------------------|
//! | `attr`  | An attribute                          | `syntax::ast::Attribute`                |
//! | `binop` | A binary operator                     | `syntax::parse::token::BinOpToken`      |
//! | `block` | A brace-delimited statement sequence  | `syntax::ptr::P<syntax::ast::Block>`    |
//! | `delim` | A delimited token tree sequence       | `std::rc::Rc<syntax::ast::Delimited>`   |
//! | `expr`  | An expression                         | `syntax::ptr::P<syntax::ast::Expr>`     |
//! | `ident` | An identifier                         | `syntax::ast::Ident`                    |
//! | `item`  | An item                               | `syntax::ptr::P<syntax::ast::Item>`     |
//! | `lftm`  | A lifetime                            | `syntax::ast::Name`                     |
//! | `lit`   | A literal                             | `syntax::ast::Lit`                      |
//! | `meta`  | A "meta" item, as found in attributes | `syntax::ptr::P<syntax::ast::MetaItem>` |
//! | `pat`   | A pattern                             | `syntax::ptr::P<syntax::ast::Pat>`      |
//! | `path`  | A qualified name                      | `syntax::ast::Path`                     |
//! | `stmt`  | A single statement                    | `syntax::ptr::P<syntax::ast::Stmt>`     |
//! | `ty`    | A type                                | `syntax::ptr::P<syntax::ast::Ty>`       |
//! | `tok`   | A single token                        | `syntax::parse::token::Token`           |
//! | `tt`    | A single token tree                   | `syntax::ast::TokenTree`                |
//!
//! ## Sequences
//!
//! Plugin argument specifications support sequences that are very similar to the sequences in macro
//! argument specifications. For example, the following plugin argument specification matches zero
//! or more comma-separated parenthesized binary expressions.
//!
//! ```ignore
//! $(($left:ident $operator:binop $right:ident)), *
//! ```
//!
//! In addition to the `*` and `+` sequence operators, there is also a `?` operator which allows for
//! sequences with either zero or one repetitions. This operator does not support separators.  For
//! example, the following plugin argument specification can match either a binary expression or
//! nothing at all.
//!
//! ```ignore
//! $($left:ident $operator:binop $right:ident)?
//! ```
//!
//! Named specifiers that occur in sequences cannot be stored directly as their storage type because
//! there may be more than one or none at all. For this reason, named specifiers that occur in
//! sequences have the storage type of either `Vec<$type>` or `Option<$type>` where `$type` is the
//! base storage type. `Vec<$type>` is used for `*` and `+` sequences and `Option<$type>` is used
//! for `?` sequences.
//!
//! An additional level of `Vec` is added for each sequence level. For example, in the plugin
//! argument specification below, `$b:ident` occurs two sequences deep. The storage type for `b` in
//! this case would be `Vec<Vec<syntax::ast::Ident>>`.
//!
//! ```ignore
//! $($a:ident $($b:ident)*)*
//! ```
//!
//! ## Named Sequences
//!
//! There are also named sequences, which behave rather differently than regular sequences. Named
//! sequences cannot contain named specifiers and instead consist of specific token trees that you
//! wish to be counted. For example, the following plugin argument specification will match
//! either `pub struct { }` or just `struct { }`.
//!
//! ```ignore
//! $public:(pub)? struct { }
//! ```
//!
//! These named sequences allow the usage of the same suffixes as regular sequences. The `*`, `+`,
//! and `?` operators are supported and separators are supported for the `*` and `+` operators. For
//! example, the following plugin argument specification matches any number of comma-separated `A`s.
//!
//! ```ignore
//! $a:(A), *
//! ```
//!
//! Because named sequences are counted, the storage types are simply `usize` for `*` and `+` named
//! sequences and `bool` for `?`named sequences.

#![feature(plugin_registrar, quote, rustc_private)]

#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]
#![cfg_attr(feature="clippy", warn(clippy))]

extern crate rustc_plugin;
extern crate syntax;

use rustc_plugin::{Registry};

use syntax::codemap;
use syntax::ast::*;
use syntax::codemap::{Span};
use syntax::ext::base::{ExtCtxt, DummyResult, MacEager, MacResult};
use syntax::ext::build::{AstBuilder};
use syntax::parse::token::{DelimToken, Token};
use syntax::ptr::{P};
use syntax::util::small_vector::{SmallVector};

mod utility;
use utility::{AsError, AsExpr};

mod arguments;
pub use self::arguments::*;

mod specification;
pub use self::specification::*;

/// A result type suitable for reporting errors in plugins.
pub type PluginResult<T> = Result<T, (Span, String)>;

fn alter_function(
    context: &mut ExtCtxt, function: P<Item>
) -> (P<Item>, Ident, Visibility, Vec<Attribute>) {
    let ident = function.ident;
    let visibility = function.vis;
    let attributes = function.attrs.clone();

    let function = function.map(|mut f| {
        f.ident = context.ident_of(&format!("{}_", ident.name));
        f.vis = Visibility::Inherited;
        f.attrs = vec![];
        f
    });

    (function, ident, visibility, attributes)
}

fn expand_variants(
    context: &mut ExtCtxt, span: Span, variants: &[(Ident, Vec<Specifier>)]
) -> Vec<P<Variant>> {
    variants.iter().map(|v| {
        let name = v.0;
        P(context.variant(span, name, vec![quote_ty!(context, $name)]))
    }).collect()
}

fn expand_struct_fields(
    context: &mut ExtCtxt, span: Span, specification: &[Specifier]
) -> Vec<StructField> {
    let mut fields = vec![];

    macro_rules! field {
        ($name:expr, $($variant:tt)*) => ({
            let kind = StructFieldKind::NamedField(context.ident_of($name), Visibility::Inherited);
            let ty = quote_ty!(context, $($variant)*);
            let field = StructField_ { kind: kind, id: DUMMY_NODE_ID, ty: ty, attrs: vec![] };
            fields.push(codemap::respan(span, field));
        });
    }

    for specifier in specification {
        match *specifier {
            Specifier::Attr(ref name) => field!(name, ::syntax::ast::Attribute),
            Specifier::BinOp(ref name) => field!(name, ::syntax::parse::token::BinOpToken),
            Specifier::Block(ref name) => field!(name, ::syntax::ptr::P<::syntax::ast::Block>),
            Specifier::Delim(ref name) => field!(name, ::std::rc::Rc<::syntax::ast::Delimited>),
            Specifier::Expr(ref name) => field!(name, ::syntax::ptr::P<::syntax::ast::Expr>),
            Specifier::Ident(ref name) => field!(name, ::syntax::ast::Ident),
            Specifier::Item(ref name) => field!(name, ::syntax::ptr::P<::syntax::ast::Item>),
            Specifier::Lftm(ref name) => field!(name, ::syntax::ast::Name),
            Specifier::Lit(ref name) => field!(name, ::syntax::ast::Lit),
            Specifier::Meta(ref name) => field!(name, ::syntax::ptr::P<::syntax::ast::MetaItem>),
            Specifier::Pat(ref name) => field!(name, ::syntax::ptr::P<::syntax::ast::Pat>),
            Specifier::Path(ref name) => field!(name, ::syntax::ast::Path),
            Specifier::Stmt(ref name) => field!(name, ::syntax::ptr::P<::syntax::ast::Stmt>),
            Specifier::Ty(ref name) => field!(name, ::syntax::ptr::P<::syntax::ast::Ty>),
            Specifier::Tok(ref name) => field!(name, ::syntax::parse::token::Token),
            Specifier::Tt(ref name) => field!(name, ::syntax::ast::TokenTree),
            Specifier::Delimited(_, ref subspecification) => {
                fields.extend(expand_struct_fields(context, span, &subspecification));
            },
            Specifier::Sequence(amount, _, ref subspecification) => {
                let mut subfields = expand_struct_fields(context, span, &subspecification);

                for subfield in &mut subfields {
                    let ty = subfield.node.ty.clone();

                    if amount == Amount::ZeroOrOne {
                        subfield.node.ty = quote_ty!(context, ::std::option::Option<$ty>);
                    } else {
                        subfield.node.ty = quote_ty!(context, ::std::vec::Vec<$ty>);
                    }
                }

                fields.extend(subfields);
            },
            Specifier::NamedSequence(ref name, amount, _, _) => if amount == Amount::ZeroOrOne {
                field!(name, bool);
            } else {
                field!(name, usize);
            },
            _ => { },
        }
    }

    fields
}

fn expand_struct(
    context: &mut ExtCtxt, span: Span, name: Ident, specification: &[Specifier]
) -> P<Item> {
    let fields = expand_struct_fields(context, span, specification);

    if fields.is_empty() {
        quote_item!(context, struct $name;).unwrap()
    } else {
        context.item_struct(span, name, VariantData::Struct(fields, DUMMY_NODE_ID))
    }
}

fn expand_field(
    context: &mut ExtCtxt, span: Span, name: &str, get: &str, stack: &[Amount]
) -> Field {
    let get = context.ident_of(get);
    let mut expr = quote_expr!(context, _m.get($name).unwrap());

    if stack.is_empty() {
        context.field_imm(span, context.ident_of(name), quote_expr!(context, $expr.$get()))
    } else {
        let f = stack.iter().skip(1).fold(quote_expr!(context, |s| s.$get()), |f, a| {
            if *a == Amount::ZeroOrOne {
                quote_expr!(context, |s| s.as_sequence().iter().map($f).next())
            } else {
                quote_expr!(context, |s| s.as_sequence().iter().map($f).collect())
            }
        });

        if stack[0] == Amount::ZeroOrOne {
            expr = quote_expr!(context, $expr.as_sequence().iter().map($f).next());
        } else {
            expr = quote_expr!(context, $expr.as_sequence().iter().map($f).collect());
        }

        context.field_imm(span, context.ident_of(name), expr)
    }
}

fn expand_fields(
    context: &mut ExtCtxt, span: Span, specification: &[Specifier], stack: &[Amount]
) -> Vec<Field> {
    let mut fields = vec![];

    macro_rules! field {
        ($name:expr, $get:ident) => ({
            fields.push(expand_field(context, span, $name, stringify!($get), stack));
        });
    }

    for specifier in specification {
        match *specifier {
            Specifier::Attr(ref name) => field!(name, as_attr),
            Specifier::BinOp(ref name) => field!(name, as_binop),
            Specifier::Block(ref name) => field!(name, as_block),
            Specifier::Delim(ref name) => field!(name, as_delim),
            Specifier::Expr(ref name) => field!(name, as_expr),
            Specifier::Ident(ref name) => field!(name, as_ident),
            Specifier::Item(ref name) => field!(name, as_item),
            Specifier::Lftm(ref name) => field!(name, as_lftm),
            Specifier::Lit(ref name) => field!(name, as_lit),
            Specifier::Meta(ref name) => field!(name, as_meta),
            Specifier::Pat(ref name) => field!(name, as_pat),
            Specifier::Path(ref name) => field!(name, as_path),
            Specifier::Stmt(ref name) => field!(name, as_stmt),
            Specifier::Ty(ref name) => field!(name, as_ty),
            Specifier::Tok(ref name) => field!(name, as_tok),
            Specifier::Tt(ref name) => field!(name, as_tt),
            Specifier::Delimited(_, ref subspecification) => {
                fields.extend(expand_fields(context, span, &subspecification, stack));
            },
            Specifier::Sequence(amount, _, ref subspecification) => {
                let mut stack = stack.to_vec();
                stack.push(amount);
                fields.extend(expand_fields(context, span, &subspecification, &stack));
            },
            Specifier::NamedSequence(ref name, amount, _, _) => if amount == Amount::ZeroOrOne {
                fields.push(expand_field(context, span, name, "as_named_sequence_bool", &stack));
            } else {
                fields.push(expand_field(context, span, name, "as_named_sequence", &stack));
            },
            _ => { },
        }
    }

    fields
}

fn expand_parse(
    context: &mut ExtCtxt, span: Span, name: Ident, specification: &[Specifier], multiple: bool
) -> P<Item> {
    let function = if multiple {
        context.ident_of(&format!("parse{}", name.name))
    } else {
        context.ident_of("parse")
    };

    let fields = expand_fields(context, span, specification, &[]);
    let specification = specification.as_expr(context, span);

    let result = if fields.is_empty() {
        quote_expr!(context, $name)
    } else {
        let path = context.path(span, vec![name]);
        context.expr_struct(span, path, fields)
    };

    quote_item!(context,
        #[allow(non_snake_case)]
        fn $function(arguments: &[::syntax::ast::TokenTree]) -> ::easy_plugin::PluginResult<$name> {
            ::easy_plugin::parse_arguments(arguments, $specification).map(|_m| $result)
        }
    ).unwrap()
}

fn expand_enum_easy_plugin(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> PluginResult<Box<MacResult + 'static>> {
    let specification = &[
        Specifier::specific_ident("enum"),
        Specifier::Ident("arguments".into()),
        Specifier::Delimited(DelimToken::Brace, vec![
            Specifier::Sequence(Amount::ZeroOrMore, None, vec![
                Specifier::Ident("name".into()),
                Specifier::Delimited(DelimToken::Brace, vec![
                    Specifier::Sequence(Amount::ZeroOrMore, None, vec![
                        Specifier::Tt("tt".into()),
                    ]),
                ]),
                Specifier::Specific(Token::Comma),
            ]),
        ]),
        Specifier::Item("function".into()),
    ];

    let matches = try!(parse_arguments(arguments, specification));

    let arguments = matches.get("arguments").unwrap().as_ident();

    let names = matches.get("name").unwrap().as_sequence().into_iter().map(|s| s.as_ident());

    let ttss = matches.get("tt").unwrap().as_sequence().into_iter().map(|s| {
        s.as_sequence().into_iter().map(|s| s.as_tt()).collect::<Vec<_>>()
    });

    let function = matches.get("function").unwrap().as_item();

    let variants: Result<Vec<_>, _> = names.zip(ttss).map(|(n, tts)| {
        parse_specification(&tts).map(|s| (n, s))
    }).collect();

    let variants = try!(variants);

    let structs = variants.iter().map(|&(n, ref s)| {
        expand_struct(context, span, n, &s)
    }).collect::<Vec<_>>();

    let parses = variants.iter().map(|&(n, ref s)| {
        expand_parse(context, span, n, &s, true)
    }).collect::<Vec<_>>();

    let def = EnumDef { variants: expand_variants(context, span, &variants)};
    let enum_ = context.item_enum(span, arguments, def);

    let (function, identifier, visibility, attributes) = alter_function(context, function);
    let inner = function.ident;

    let mut stmts = vec![];

    let mut variants = variants.iter().peekable();

    while let Some(variant) = variants.next() {
        let parse = context.ident_of(&format!("parse{}", variant.0.name));
        let constructor = variant.0;

        let stmt = if variants.peek().is_some() {
            quote_stmt!(context,
                if let Ok(result) = $parse(arguments).and_then(|a| {
                    $inner(context, span, $arguments::$constructor(a))
                }) {
                    return result;
                }
            )
        } else {
            quote_stmt!(context,
                return match $parse(arguments).and_then(|a| {
                    $inner(context, span, $arguments::$constructor(a))
                }) {
                    Ok(result) => result,
                    Err((span, message)) => {
                        context.span_err(span, &message);
                        ::syntax::ext::base::DummyResult::any(span)
                    }
                };
            )
        };

        stmts.push(stmt);
    }

    let mut item = quote_item!(context,
        fn $identifier(
            context: &mut ::syntax::ext::base::ExtCtxt,
            span: ::syntax::codemap::Span,
            arguments: &[::syntax::ast::TokenTree],
        ) -> ::std::boxed::Box<::syntax::ext::base::MacResult> {
            $structs
            $enum_
            $parses
            $function
            $stmts
        }
    ).unwrap();

    item = item.map(|mut i| {
        i.vis = visibility;
        i.attrs = attributes;
        i
    });

    Ok(MacEager::items(SmallVector::one(item)))
}

fn expand_struct_easy_plugin(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> PluginResult<Box<MacResult + 'static>> {
    let specification = &[
        Specifier::specific_ident("struct"),
        Specifier::Ident("arguments".into()),
        Specifier::Delimited(DelimToken::Brace, vec![
            Specifier::Sequence(Amount::ZeroOrMore, None, vec![
                Specifier::Tt("tt".into()),
            ]),
        ]),
        Specifier::Item("function".into()),
    ];

    let matches = try!(parse_arguments(arguments, specification));

    let arguments = matches.get("arguments").unwrap().as_ident();

    let tts = matches.get("tt").unwrap().as_sequence().iter().map(|s| {
        s.as_tt()
    }).collect::<Vec<_>>();

    let function = matches.get("function").unwrap().as_item();

    let specification = try!(parse_specification(&tts));
    let struct_ = expand_struct(context, span, arguments, &specification);
    let parse = expand_parse(context, span, arguments, &specification, false);
    let (function, identifier, visibility, attributes) = alter_function(context, function);
    let inner = function.ident;

    let mut item = quote_item!(context,
        fn $identifier(
            context: &mut ::syntax::ext::base::ExtCtxt,
            span: ::syntax::codemap::Span,
            arguments: &[::syntax::ast::TokenTree],
        ) -> ::std::boxed::Box<::syntax::ext::base::MacResult> {
            $struct_
            $parse
            $function
            match parse(arguments).and_then(|a| $inner(context, span, a)) {
                Ok(result) => result,
                Err((span, message)) => {
                    context.span_err(span, &message);
                    ::syntax::ext::base::DummyResult::any(span)
                },
            }
        }
    ).unwrap();

    item = item.map(|mut i| {
        i.vis = visibility;
        i.attrs = attributes;
        i
    });

    Ok(MacEager::items(SmallVector::one(item)))
}

fn expand_easy_plugin_(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> PluginResult<Box<MacResult + 'static>> {
    if arguments.is_empty() {
        return span.as_error("unexpected end of arguments");
    }

    match arguments[0] {
        TokenTree::Token(_, Token::Ident(ref ident, _)) => match &*ident.name.as_str() {
            "enum" => expand_enum_easy_plugin(context, span, arguments),
            "struct" => expand_struct_easy_plugin(context, span, arguments),
            _ => arguments[0].as_error("expected `enum` or `struct`"),
        },
        _ => arguments[0].as_error("expected `enum` or `struct`"),
    }
}

#[doc(hidden)]
pub fn expand_easy_plugin(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> Box<MacResult + 'static> {
    match expand_easy_plugin_(context, span, arguments) {
        Ok(result) => result,
        Err((span, message)) => {
            context.span_err(span, &message);
            DummyResult::any(span)
        },
    }
}

#[doc(hidden)]
#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("parse_specification", expand_parse_specification);
    registry.register_macro("easy_plugin", expand_easy_plugin);
}
