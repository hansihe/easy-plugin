use syntax::ast::*;
use syntax::codemap::{Span, Spanned};
use syntax::ext::base::{ExtCtxt, MacEager, MacResult};
use syntax::ext::build::{AstBuilder};
use syntax::parse::token::{DelimToken};
use syntax::ptr::{P};
use syntax::util::small_vector::{SmallVector};
use syntax::tokenstream::{TokenTree};

use super::*;

//================================================
// Functions
//================================================

/// Returns a struct that stores the values matched by the supplied specification.
pub fn expand_struct(
    context: &mut ExtCtxt, span: Span, name: Ident, specification: &Specification
) -> P<Item> {
    let fields = specification.iter().flat_map(|s| {
        s.to_struct_fields(context, span).into_iter()
    }).collect::<Vec<_>>();

    // Build the struct.
    let struct_ = if fields.is_empty() {
        quote_item!(context, struct $name;).unwrap()
    } else {
        context.item_struct(span, name, VariantData::Struct(fields, DUMMY_NODE_ID))
    };
    struct_.map(|mut s| {
        s.attrs = vec![quote_attr!(context, #[derive(Clone, Debug)])];
        s
    })
}

fn expand_easy_plugin_struct_(
    context: &mut ExtCtxt, span: Span, arguments: Ident, tts: Vec<TokenTree>, function: P<Item>
) -> PluginResult<Box<MacResult + 'static>> {
    let specification = try!(super::parse_spec(&tts));

    let struct_ = expand_struct(context, span, arguments, &specification);
    let parse = super::expand_parse(context, span, arguments, &specification, false);
    let (function, identifier, visibility, attributes) = strip_function(context, function);
    let inner = function.ident;

    // Build the wrapper function.
    let item = quote_item!(context,
        fn $identifier(
            context: &mut ::syntax::ext::base::ExtCtxt,
            span: ::syntax::codemap::Span,
            arguments: &[::syntax::tokenstream::TokenTree],
        ) -> ::std::boxed::Box<::syntax::ext::base::MacResult> {
            $struct_
            $parse
            $function
            match parse(context.parse_sess, arguments).and_then(|a| $inner(context, span, a)) {
                Ok(result) => result,
                Err((subspan, message)) => {
                    let span = if subspan == ::syntax::codemap::DUMMY_SP {
                        span
                    } else {
                        subspan
                    };

                    context.span_err(span, &message);
                    ::syntax::ext::base::DummyResult::any(span)
                },
            }
        }
    ).unwrap().map(|mut i| {
        i.vis = visibility;
        i.attrs = attributes;
        i
    });
    Ok(MacEager::items(SmallVector::one(item)))
}

/// Returns a single specification `easy-plugin` wrapper function.
pub fn expand_easy_plugin_struct(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> PluginResult<Box<MacResult + 'static>> {
    // Build the argument specification.
    let specification = &[
        Specifier::specific_ident("struct"),
        Specifier::Ident("arguments".into()),
        Specifier::Delimited(DelimToken::Brace, spec![
            Specifier::Sequence(Amount::ZeroOrMore, None, spec![
                Specifier::Tt("tt".into()),
            ]),
        ]),
        Specifier::Item("function".into()),
    ];

    // Extract the arguments.
    let matches = try!(parse_args(context.parse_sess, arguments, specification));
    let arguments = matches.get("arguments").unwrap().to::<Spanned<Ident>>().node;
    let tts = matches.get("tt").unwrap().to::<Vec<Match>>().iter().map(|s| {
        s.to::<TokenTree>()
    }).collect::<Vec<_>>();
    let function = matches.get("function").unwrap().to::<P<Item>>();

    expand_easy_plugin_struct_(context, span, arguments, tts, function)
}
