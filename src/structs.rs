use syntax::ast::*;
use syntax::codemap::{Span, Spanned};
use syntax::ext::base::{ExtCtxt, MacEager, MacResult};
use syntax::parse::token::{DelimToken};
use syntax::ptr::{P};
use syntax::util::small_vector::{SmallVector};
use syntax::tokenstream::{TokenTree};

use super::*;

//================================================
// Functions
//================================================

fn expand_easy_plugin_struct_(
    context: &mut ExtCtxt, span: Span, arguments: Ident, tts: Vec<TokenTree>, function: P<Item>
) -> PluginResult<Box<MacResult + 'static>> {
    let specification = try!(parse_spec(&tts));
    let (function, identifier, visibility, attributes) = strip_function(context, function);

    let expr = quote_expr!(context, |a| ${function.ident}(context, span, a));
    let expr = quote_expr!(context, parse(context.parse_sess, arguments).and_then($expr));

    let item = quote_item!(context,
        $attributes
        $visibility fn $identifier(
            context: &mut ::syntax::ext::base::ExtCtxt,
            span: ::syntax::codemap::Span,
            arguments: &[::syntax::tokenstream::TokenTree],
        ) -> Box<::syntax::ext::base::MacResult> {
            ${specification.to_struct_item(context, arguments)}
            ${expand_parse_fn(context, span, arguments, &specification, false)}
            $function
            ${expand_parse_expr(context, expr)}
        }
    ).unwrap();
    Ok(MacEager::items(SmallVector::one(item)))
}

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
