use std::marker::{PhantomData};

use syntax::print::pprust;
use syntax::ast::{Ident, TokenTree};
use syntax::codemap::{Span};
use syntax::parse::token::{Token};

use super::{PluginResult, SpanAsError};

pub struct TtsIterator<'i, I> where I: Iterator<Item=&'i TokenTree> {
    pub error: (Span, String),
    pub iterator: I,
    lifetime: PhantomData<&'i ()>,
}

impl<'i, I> TtsIterator<'i, I> where I: Iterator<Item=&'i TokenTree> {
    pub fn new(iterator: I, span: Span, message: &str) -> TtsIterator<'i, I> {
        TtsIterator { error: (span, message.into()), iterator: iterator, lifetime: PhantomData }
    }

    pub fn expect(&mut self) -> PluginResult<&'i TokenTree> {
        self.iterator.next().ok_or_else(|| self.error.clone())
    }

    pub fn expect_token(&mut self, description: &str) -> PluginResult<(Span, &'i Token)> {
        self.expect().and_then(|tt| {
            match *tt {
                TokenTree::TtToken(span, ref token) => Ok((span, token)),
                _ => tt.as_error(format!("expected {}", description)),
            }
        })
    }

    pub fn expect_specific_token(&mut self, token: &Token) -> PluginResult<()> {
        let description = get_description(token);

        self.expect_token(&get_description(token)).and_then(|(s, t)| {
            if t.mtwt_eq(token) {
                Ok(())
            } else {
                s.as_error(format!("expected {}", description))
            }
        })
    }

    pub fn expect_ident(&mut self) -> PluginResult<(Span, Ident)> {
        self.expect_token("identifier").and_then(|(s, t)| {
            match *t {
                Token::Ident(ref ident, _) => Ok((s, ident.clone())),
                _ => s.as_error("expected identifier"),
            }
        })
    }
}

impl<'i, I> Iterator for TtsIterator<'i, I> where I: Iterator<Item=&'i TokenTree> {
    type Item = &'i TokenTree;

    fn next(&mut self) -> Option<&'i TokenTree> {
        self.iterator.next()
    }
}

fn get_description(token: &Token) -> String {
    match *token {
        Token::BinOp(_) |
        Token::BinOpEq(_) => format!("binary operator (`{}`)", pprust::token_to_string(token)),
        Token::Literal(_, _) => format!("literal (`{}`)", pprust::token_to_string(token)),
        Token::Ident(_, _) => format!("identifier (`{}`)", pprust::token_to_string(token)),
        Token::Lifetime(_) => format!("lifetime (`{}`)", pprust::token_to_string(token)),
        _ => format!("`{}`", pprust::token_to_string(token)),
    }
}
