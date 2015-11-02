use std::collections::{HashSet};

use syntax::ast::{KleeneOp, TokenTree};
use syntax::codemap::{DUMMY_SP, Span};
use syntax::parse::token::{BinOpToken, DelimToken, Token};

use super::{PluginResult};
use super::utility::{SpanAsError, TtsIterator};

/// A piece of a plugin argument specification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Specifier {
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
    Sequence(KleeneOp, Option<Token>, Vec<Specifier>),
}

fn parse_dollar<'i, I>(
    span: Span, tts: &mut TtsIterator<'i, I>, names: &mut HashSet<String>
) -> PluginResult<Specifier> where I: Iterator<Item=&'i TokenTree> {
    match try!(tts.expect()) {
        &TokenTree::TtToken(subspan, Token::Ident(ref ident, _)) => {
            let name = ident.name.as_str().to_string();

            if !names.insert(name.clone()) {
                subspan.as_error("duplicate named specifier")
            } else {
                parse_named_specifier(tts, name)
            }
        },
        &TokenTree::TtDelimited(_, ref delimited) => {
            parse_sequence(span, tts, &delimited.tts, names)
        },
        invalid => invalid.as_error("expected named specifier or sequence"),
    }
}

fn parse_named_specifier<'i, I>(
    tts: &mut TtsIterator<'i, I>, name: String
) -> PluginResult<Specifier> where I: Iterator<Item=&'i TokenTree> {
    try!(tts.expect_specific_token(&Token::Colon));
    let (subspan, value) = try!(tts.expect_ident());

    match &*value.name.as_str() {
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
    }
}

fn parse_sequence<'i, I>(
    span: Span, tts: &mut TtsIterator<'i, I>, subtts: &[TokenTree], names: &mut HashSet<String>
) -> PluginResult<Specifier> where I: Iterator<Item=&'i TokenTree> {
    let subspecification = try!(parse_specification_(span, subtts, names));

    let (kleene, separator) = match try!(tts.expect_token("expected separator, `*`, or `+`")) {
        (_, &Token::BinOp(BinOpToken::Star)) => (KleeneOp::ZeroOrMore, None),
        (_, &Token::BinOp(BinOpToken::Plus)) => (KleeneOp::OneOrMore, None),
        (subspan, separator) => match try!(tts.expect_token("expected `*` or `+`")) {
            (_, &Token::BinOp(BinOpToken::Star)) => (KleeneOp::ZeroOrMore, Some(separator.clone())),
            (_, &Token::BinOp(BinOpToken::Plus)) => (KleeneOp::OneOrMore, Some(separator.clone())),
            _ => return subspan.as_error("expected `*` or `+`"),
        },
    };

    Ok(Specifier::Sequence(kleene, separator, subspecification))
}

fn parse_specification_(
    span: Span, tts: &[TokenTree], names: &mut HashSet<String>
) -> PluginResult<Vec<Specifier>> {
    let mut tts = TtsIterator::new(tts.iter(), span, "unexpected end of specification");

    let mut specification = vec![];

    while let Some(tt) = tts.next() {
        match *tt {
            TokenTree::TtToken(_, Token::Dollar) => {
                specification.push(try!(parse_dollar(span, &mut tts, names)));
            },
            TokenTree::TtToken(_, ref token) => {
                specification.push(Specifier::Specific(token.clone()));
            },
            TokenTree::TtDelimited(subspan, ref delimited) => {
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
    let start = tts.iter().nth(0).map(|s| s.get_span()).unwrap_or(DUMMY_SP);
    let end = tts.iter().last().map(|s| s.get_span()).unwrap_or(DUMMY_SP);
    let span = Span { lo: start.lo, hi: end.hi, expn_id: start.expn_id };
    parse_specification_(span, tts, &mut HashSet::new())
}

#[cfg(test)]
mod tests {
    use super::*;

    use syntax::parse;
    use syntax::parse::token;
    use syntax::ast::{Ident, KleeneOp, TokenTree};
    use syntax::parse::{ParseSess};
    use syntax::parse::token::{DelimToken, IdentStyle, Token};

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

        with_tts("$a:binop $b:tt", |tts| {
            assert_eq!(parse_specification(&tts).unwrap(), vec![
                Specifier::BinOp("a".into()),
                Specifier::Tt("b".into()),
            ]);
        });

        with_tts("$($a:ident $($b:ident)*), +", |tts| {
            assert_eq!(parse_specification(&tts).unwrap(), vec![
                Specifier::Sequence(KleeneOp::OneOrMore, Some(Token::Comma), vec![
                    Specifier::Ident("a".into()),
                    Specifier::Sequence(KleeneOp::ZeroOrMore, None, vec![
                        Specifier::Ident("b".into()),
                    ]),
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
            let foo = Token::Ident(Ident::with_empty_ctxt(token::intern("foo")), IdentStyle::Plain);
            let bar = Token::Lifetime(Ident::with_empty_ctxt(token::intern("'bar")));

            assert_eq!(parse_specification(&tts).unwrap(), vec![
                Specifier::Specific(Token::Tilde),
                Specifier::Specific(foo),
                Specifier::Specific(bar),
            ]);
        });
    }
}
