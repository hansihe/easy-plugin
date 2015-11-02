use std::marker::{PhantomData};

use syntax::ast::{Ident, TokenTree};
use syntax::codemap::{Span};
use syntax::parse::parser::{Parser};
use syntax::parse::token::{Token};

use super::{PluginResult};

pub trait SpanAsError<T, S> where S: AsRef<str> {
    fn as_error(&self, message: S) -> PluginResult<T>;
}

impl<T, S> SpanAsError<T, S> for Span where S: AsRef<str> {
    fn as_error(&self, message: S) -> PluginResult<T> {
        Err((self.clone(), message.as_ref().into()))
    }
}

impl<T, S> SpanAsError<T, S> for TokenTree where S: AsRef<str> {
    fn as_error(&self, message: S) -> PluginResult<T> {
        Err((self.get_span().clone(), message.as_ref().into()))
    }
}

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
        let description = Parser::token_to_string(token);

        self.expect_token(&description).and_then(|(s, t)| {
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
