use syntax::ast::*;
use syntax::codemap::{Span, Spanned};
use syntax::ext::base::{ExtCtxt, MacEager, MacResult};
use syntax::ext::build::{AstBuilder};
use syntax::parse::token::{DelimToken, Token};
use syntax::ptr::{P};
use syntax::util::small_vector::{SmallVector};
use syntax::tokenstream::{TokenTree};

use super::*;
use super::structs;

//================================================
// Functions
//================================================

fn expand_easy_plugin_enum_(
    context: &mut ExtCtxt,
    span: Span,
    arguments: Ident,
    names: Vec<Ident>,
    ttss: Vec<Vec<TokenTree>>,
    function: P<Item>,
) -> PluginResult<Box<MacResult + 'static>> {
    let specifications: Result<Vec<_>, _> = names.iter().zip(ttss.into_iter()).map(|(n, tts)| {
        parse_spec(&tts).map(|s| (*n, s))
    }).collect();
    let specifications = try!(specifications);

    let structs = specifications.iter().map(|&(n, ref s)| {
        structs::expand_struct(context, span, n, s)
    }).collect::<Vec<_>>();
    let variants = names.iter().map(|n| {
        context.variant(span, *n, vec![quote_ty!(context, $n)])
    }).collect();
    let enum_ = context.item_enum(span, arguments, EnumDef { variants: variants }).map(|mut e| {
        e.attrs = vec![quote_attr!(context, #[derive(Clone, Debug)])];
        e
    });

    let parses = specifications.iter().map(|&(n, ref s)| {
        expand_parse(context, span, n, s, true)
    }).collect::<Vec<_>>();

    let (function, identifier, visibility, attributes) = strip_function(context, function);
    let inner = function.ident;

    let stmts = names.iter().enumerate().map(|(i, ref n)| {
        let parse = context.ident_of(&format!("parse{}", n));
        if i + 1 < specifications.len() {
            quote_stmt!(context,
                if let Ok(arguments) = $parse(context.parse_sess, arguments) {
                    return match $inner(context, span, $arguments::$n(arguments)) {
                        Ok(result) => result,
                        Err((subspan, message)) => {
                            let span = if subspan == ::syntax::codemap::DUMMY_SP {
                                span
                            } else {
                                subspan
                            };

                            context.span_err(span, &message);
                            ::syntax::ext::base::DummyResult::any(span)
                        }
                    };
                }
            )
        } else {
            quote_stmt!(context,
                return match $parse(context.parse_sess, arguments).and_then(|a| {
                    $inner(context, span, $arguments::$n(a))
                }) {
                    Ok(result) => result,
                    Err((subspan, message)) => {
                        let span = if subspan == ::syntax::codemap::DUMMY_SP {
                            span
                        } else {
                            subspan
                        };

                        context.span_err(span, &message);
                        ::syntax::ext::base::DummyResult::any(span)
                    }
                };
            )
        }
    }).collect::<Vec<_>>();

    // Build the wrapper function.
    let item = quote_item!(context,
        fn $identifier(
            context: &mut ::syntax::ext::base::ExtCtxt,
            span: ::syntax::codemap::Span,
            arguments: &[::syntax::tokenstream::TokenTree],
        ) -> ::std::boxed::Box<::syntax::ext::base::MacResult> {
            $structs
            $enum_
            $parses
            $function
            $stmts
        }
    ).unwrap().map(|mut i| {
        i.vis = visibility;
        i.attrs = attributes;
        i
    });
    Ok(MacEager::items(SmallVector::one(item)))
}

/// Returns a mulitple specification `easy-plugin` wrapper function.
pub fn expand_easy_plugin_enum(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> PluginResult<Box<MacResult + 'static>> {
    // Build the argument specification.
    let specification = &[
        Specifier::specific_ident("enum"),
        Specifier::Ident("arguments".into()),
        Specifier::Delimited(DelimToken::Brace, spec![
            Specifier::Sequence(Amount::ZeroOrMore, None, spec![
                Specifier::Ident("name".into()),
                Specifier::Delimited(DelimToken::Brace, spec![
                    Specifier::Sequence(Amount::ZeroOrMore, None, spec![
                        Specifier::Tt("tt".into()),
                    ]),
                ]),
                Specifier::Specific(Token::Comma),
            ]),
        ]),
        Specifier::Item("function".into()),
    ];

    // Extract the arguments.
    let matches = try!(parse_args(context.parse_sess, arguments, specification));
    let arguments = matches.get("arguments").unwrap().to::<Spanned<Ident>>().node;
    let names = matches.get("name").unwrap().to::<Vec<Match>>().into_iter().map(|s| {
        s.to::<Spanned<Ident>>().node
    }).collect();
    let ttss = matches.get("tt").unwrap().to::<Vec<Match>>().into_iter().map(|s| {
        s.to::<Vec<Match>>().into_iter().map(|s| s.to::<TokenTree>()).collect::<Vec<_>>()
    }).collect();
    let function = matches.get("function").unwrap().to::<P<Item>>();

    expand_easy_plugin_enum_(context, span, arguments, names, ttss, function)
}
