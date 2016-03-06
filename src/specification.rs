use std::collections::{HashSet};

use syntax::parse::token;
use syntax::ast::{Expr, Ident, TokenTree};
use syntax::ext::base::{DummyResult, ExtCtxt, MacEager, MacResult};
use syntax::ext::build::{AstBuilder};
use syntax::codemap::{DUMMY_SP, Span};
use syntax::parse::token::{BinOpToken, DelimToken, IdentStyle, Token};
use syntax::ptr::{P};

use super::{PluginResult};
use super::utility::{AsError, AsExpr, TtsIterator};

//================================================
// Enums
//================================================

// Amount ________________________________________

/// Indicates how many times a sequence is allowed to occur.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Amount {
    OneOrMore,
    ZeroOrMore,
    ZeroOrOne,
}

impl AsExpr for Amount {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let path = vec![
            context.ident_of("easy_plugin"),
            context.ident_of("Amount"),
            context.ident_of(&format!("{:?}", self)),
        ];

        context.expr_path(context.path_global(span, path))
    }
}

// Specifier _____________________________________

/// A piece of a plugin argument specification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Specifier {
    /// An attribute (e.g., `#[cfg(target_os = "windows")]`).
    Attr(String),
    /// A binary operator (e.g., `+`, `*`).
    BinOp(String),
    /// A brace-delimited sequence of statements (e.g., `{ log(error, "hi"); return 12; }`).
    Block(String),
    /// A delimited sequence of token trees (e.g., `()`, `[foo - "bar"]`).
    Delim(String),
    /// An expression (e.g., `2 + 2`, `if true { 1 } else { 2 }`, `f(42)`).
    Expr(String),
    /// An identifier (e.g., `x`, `foo`).
    Ident(String),
    /// An item (e.g., `fn foo() { }`, `struct Bar;`).
    Item(String),
    /// A lifetime (e.g., `'a`).
    Lftm(String),
    /// A literal (e.g., `322`, `'a'`, `"foo"`).
    Lit(String),
    /// A "meta" item, as found in attributes (e.g., `cfg(target_os = "windows")`).
    Meta(String),
    /// A pattern (e.g., `Some(t)`, `(17, 'a')`, `_`).
    Pat(String),
    /// A qualified name (e.g., `T::SpecialA`).
    Path(String),
    /// A single statement (e.g., `let x = 3`).
    Stmt(String),
    /// A type (e.g., `i32`, `Vec<(char, String)>`, `&T`).
    Ty(String),
    /// A single token.
    Tok(String),
    /// A single token tree.
    Tt(String),
    /// A non-variable piece.
    Specific(Token),
    /// A delimited piece.
    Delimited(DelimToken, Vec<Specifier>),
    /// A sequence piece.
    Sequence(Amount, Option<Token>, Vec<Specifier>),
    /// A named sequence piece.
    NamedSequence(String, Amount, Option<Token>, Vec<Specifier>),
}

impl AsExpr for Specifier {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        macro_rules! expr {
            ($variant:expr, $($argument:expr), *) => ({
                let path = vec![
                    context.ident_of("easy_plugin"),
                    context.ident_of("Specifier"),
                    context.ident_of($variant),
                ];

                let arguments = vec![$($argument), *];
                context.expr_call_global(span, path, arguments)
            });
        }

        macro_rules! string {
            ($name:expr) => ({
                let name = context.expr_str(span, context.name_of($name).as_str());
                let into = context.ident_of("into");
                context.expr_method_call(span, name, into, vec![])
            });
        }

        match *self {
            Specifier::Attr(ref name) => expr!("Attr", string!(name)),
            Specifier::BinOp(ref name) => expr!("BinOp", string!(name)),
            Specifier::Block(ref name) => expr!("Block", string!(name)),
            Specifier::Delim(ref name) => expr!("Delim", string!(name)),
            Specifier::Expr(ref name) => expr!("Expr", string!(name)),
            Specifier::Ident(ref name) => expr!("Ident", string!(name)),
            Specifier::Item(ref name) => expr!("Item", string!(name)),
            Specifier::Lftm(ref name) => expr!("Lftm", string!(name)),
            Specifier::Lit(ref name) => expr!("Lit", string!(name)),
            Specifier::Meta(ref name) => expr!("Meta", string!(name)),
            Specifier::Pat(ref name) => expr!("Pat", string!(name)),
            Specifier::Path(ref name) => expr!("Path", string!(name)),
            Specifier::Stmt(ref name) => expr!("Stmt", string!(name)),
            Specifier::Ty(ref name) => expr!("Ty", string!(name)),
            Specifier::Tok(ref name) => expr!("Tok", string!(name)),
            Specifier::Tt(ref name) => expr!("Tt", string!(name)),
            Specifier::Specific(ref token) => expr!("Specific", token.as_expr(context, span)),
            Specifier::Delimited(delimiter, ref subspecification) => {
                let subspecification = subspecification.as_expr(context, span);
                expr!("Delimited", delimiter.as_expr(context, span), subspecification)
            },
            Specifier::Sequence(amount, ref separator, ref subspecification) => {
                let amount = amount.as_expr(context, span);
                let separator = separator.as_expr(context, span);
                let subspecification = subspecification.as_expr(context, span);
                expr!("Sequence", amount, separator, subspecification)
            },
            Specifier::NamedSequence(ref name, amount, ref separator, ref subspecification) => {
                let amount = amount.as_expr(context, span);
                let separator = separator.as_expr(context, span);
                let subspecification = subspecification.as_expr(context, span);
                expr!("NamedSequence", string!(name), amount, separator, subspecification)
            },
        }
    }
}

impl Specifier {
    /// Returns a new `Specifier` corresponding to the given identifier.
    pub fn specific_ident(ident: &str) -> Specifier {
        let ident = Ident::with_empty_ctxt(token::intern(ident));
        Specifier::Specific(Token::Ident(ident, IdentStyle::Plain))
    }

    /// Returns a new `Specifier` corresponding to the given lifetime.
    pub fn specific_lftm(lftm: &str) -> Specifier {
        let lftm = Ident::with_empty_ctxt(token::intern(lftm));
        Specifier::Specific(Token::Lifetime(lftm))
    }
}

//================================================
// Functions
//================================================

fn parse_dollar<'i, I>(
    span: Span, tts: &mut TtsIterator<'i, I>, names: &mut HashSet<String>
) -> PluginResult<Specifier> where I: Iterator<Item=&'i TokenTree> {
    match try!(tts.expect()) {
        &TokenTree::Token(subspan, Token::Ident(ref ident, _)) => {
            let name = ident.name.as_str().to_string();

            if names.insert(name.clone()) {
                parse_named_specifier(tts, name)
            } else {
                subspan.as_error("duplicate named specifier")
            }
        },
        &TokenTree::Delimited(_, ref delimited) => {
            parse_sequence(span, tts, &delimited.tts, names)
        },
        invalid => invalid.as_error("expected named specifier or sequence"),
    }
}

fn parse_named_specifier<'i, I>(
    tts: &mut TtsIterator<'i, I>, name: String
) -> PluginResult<Specifier> where I: Iterator<Item=&'i TokenTree> {
    try!(tts.expect_specific_token(&Token::Colon));

    match try!(tts.expect()) {
        &TokenTree::Delimited(subspan, ref delimited) => {
            let mut names = HashSet::new();
            let subspecification = try!(parse_specification_(subspan, &delimited.tts, &mut names));

            if !names.is_empty() {
                return subspan.as_error("named specifiers not allowed in named sequences");
            }

            let (amount, separator) = try!(parse_sequence_suffix(tts));
            Ok(Specifier::NamedSequence(name, amount, separator, subspecification))
        },
        &TokenTree::Token(subspan, Token::Ident(ref ident, _)) => match &*ident.name.as_str() {
            "attr" => Ok(Specifier::Attr(name)),
            "binop" => Ok(Specifier::BinOp(name)),
            "block" => Ok(Specifier::Block(name)),
            "delim" => Ok(Specifier::Delim(name)),
            "expr" => Ok(Specifier::Expr(name)),
            "ident" => Ok(Specifier::Ident(name)),
            "item" => Ok(Specifier::Item(name)),
            "lftm" => Ok(Specifier::Lftm(name)),
            "lit" => Ok(Specifier::Lit(name)),
            "meta" => Ok(Specifier::Meta(name)),
            "pat" => Ok(Specifier::Pat(name)),
            "path" => Ok(Specifier::Path(name)),
            "stmt" => Ok(Specifier::Stmt(name)),
            "ty" => Ok(Specifier::Ty(name)),
            "tok" => Ok(Specifier::Tok(name)),
            "tt" => Ok(Specifier::Tt(name)),
            _ => subspan.as_error("invalid named specifier type"),
        },
        invalid => invalid.as_error("expected named specifier type or sequence"),
    }
}

fn parse_sequence_suffix<'i, I>(
    tts: &mut TtsIterator<'i, I>
) -> PluginResult<(Amount, Option<Token>)> where I: Iterator<Item=&'i TokenTree> {
    match try!(tts.expect_token("expected separator, `*`, or `+`")) {
        (_, &Token::BinOp(BinOpToken::Plus)) => Ok((Amount::OneOrMore, None)),
        (_, &Token::BinOp(BinOpToken::Star)) => Ok((Amount::ZeroOrMore, None)),
        (_, &Token::Question) => Ok((Amount::ZeroOrOne, None)),
        (subspan, separator) => match try!(tts.expect_token("expected `*` or `+`")) {
            (_, &Token::BinOp(BinOpToken::Plus)) => Ok((Amount::OneOrMore, Some(separator.clone()))),
            (_, &Token::BinOp(BinOpToken::Star)) => Ok((Amount::ZeroOrMore, Some(separator.clone()))),
            _ => subspan.as_error("expected `*` or `+`"),
        },
    }
}

fn parse_sequence<'i, I>(
    span: Span, tts: &mut TtsIterator<'i, I>, subtts: &[TokenTree], names: &mut HashSet<String>
) -> PluginResult<Specifier> where I: Iterator<Item=&'i TokenTree> {
    let subspecification = try!(parse_specification_(span, subtts, names));
    let (amount, separator) = try!(parse_sequence_suffix(tts));
    Ok(Specifier::Sequence(amount, separator, subspecification))
}

fn parse_specification_(
    span: Span, tts: &[TokenTree], names: &mut HashSet<String>
) -> PluginResult<Vec<Specifier>> {
    let mut tts = TtsIterator::new(tts.iter(), span, "unexpected end of specification");

    let mut specification = vec![];

    while let Some(tt) = tts.next() {
        match *tt {
            TokenTree::Token(_, Token::Dollar) => {
                specification.push(try!(parse_dollar(span, &mut tts, names)));
            },
            TokenTree::Token(_, ref token) => {
                specification.push(Specifier::Specific(token.clone()));
            },
            TokenTree::Delimited(subspan, ref delimited) => {
                let subspecification = try!(parse_specification_(subspan, &delimited.tts, names));
                specification.push(Specifier::Delimited(delimited.delim, subspecification));
            },
            _ => unreachable!(),
        }
    }

    Ok(specification)
}

/// Parses the given specification.
pub fn parse_specification(tts: &[TokenTree]) -> PluginResult<Vec<Specifier>> {
    let start = tts.iter().nth(0).map_or(DUMMY_SP, |s| s.get_span());
    let end = tts.iter().last().map_or(DUMMY_SP, |s| s.get_span());
    let span = Span { lo: start.lo, hi: end.hi, expn_id: start.expn_id };
    parse_specification_(span, tts, &mut HashSet::new())
}

#[doc(hidden)]
pub fn expand_parse_specification(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> Box<MacResult> {
    match parse_specification(arguments) {
        Ok(specification) => {
            let exprs = specification.iter().map(|s| s.as_expr(context, span)).collect();
            MacEager::expr(context.expr_vec_slice(span, exprs))
        },
        Err((span, message)) => {
            context.span_err(span, &message);
            DummyResult::any(span)
        },
    }
}

//================================================
// Tests
//================================================

#[cfg(test)]
mod tests {
    use super::*;

    use syntax::parse;
    use syntax::ast::{TokenTree};
    use syntax::parse::{ParseSess};
    use syntax::parse::token::{DelimToken, Token};

    fn with_tts<F>(source: &str, f: F) where F: Fn(Vec<TokenTree>) {
        let session = ParseSess::new();
        let source = source.into();
        let mut parser = parse::new_parser_from_source_str(&session, vec![], "".into(), source);
        f(parser.parse_all_token_trees().unwrap());
    }

    #[test]
    fn test_parse_specification() {
        with_tts("", |tts| {
            assert_eq!(parse_specification(&tts).unwrap(), vec![]);
        });

        with_tts("$a:attr $b:tt", |tts| {
            assert_eq!(parse_specification(&tts).unwrap(), vec![
                Specifier::Attr("a".into()),
                Specifier::Tt("b".into()),
            ]);
        });

        with_tts("$($a:ident $($b:ident)*), + $($c:ident)?", |tts| {
            assert_eq!(parse_specification(&tts).unwrap(), vec![
                Specifier::Sequence(Amount::OneOrMore, Some(Token::Comma), vec![
                    Specifier::Ident("a".into()),
                    Specifier::Sequence(Amount::ZeroOrMore, None, vec![
                        Specifier::Ident("b".into()),
                    ]),
                ]),
                Specifier::Sequence(Amount::ZeroOrOne, None, vec![
                    Specifier::Ident("c".into()),
                ]),
            ]);
        });

        with_tts("$a:(A)* $b:(B), + $c:(C)?", |tts| {
            assert_eq!(parse_specification(&tts).unwrap(), vec![
                Specifier::NamedSequence("a".into(), Amount::ZeroOrMore, None, vec![
                    Specifier::specific_ident("A"),
                ]),
                Specifier::NamedSequence("b".into(), Amount::OneOrMore, Some(Token::Comma), vec![
                    Specifier::specific_ident("B"),
                ]),
                Specifier::NamedSequence("c".into(), Amount::ZeroOrOne, None, vec![
                    Specifier::specific_ident("C"),
                ]),
            ]);
        });

        with_tts("() [$a:ident] {$b:ident $c:ident}", |tts| {
            assert_eq!(parse_specification(&tts).unwrap(), vec![
                Specifier::Delimited(DelimToken::Paren, vec![]),
                Specifier::Delimited(DelimToken::Bracket, vec![
                    Specifier::Ident("a".into()),
                ]),
                Specifier::Delimited(DelimToken::Brace, vec![
                    Specifier::Ident("b".into()),
                    Specifier::Ident("c".into()),
                ]),
            ]);
        });

        with_tts("~ foo 'bar", |tts| {
            assert_eq!(parse_specification(&tts).unwrap(), vec![
                Specifier::Specific(Token::Tilde),
                Specifier::specific_ident("foo"),
                Specifier::specific_lftm("'bar"),
            ]);
        });
    }
}
