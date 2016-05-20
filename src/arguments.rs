// Copyright 2016 Kyle Mayes
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::collections::{HashMap};
use std::rc::{Rc};

use syntax::ast::*;
use syntax::codemap::{self, DUMMY_SP, CodeMap, Span, Spanned};
use syntax::errors::{Handler};
use syntax::parse::{ParseSess};
use syntax::parse::common::{SeqSep};
use syntax::parse::parser::{Parser};
use syntax::parse::token::{BinOpToken, Token};
use syntax::ptr::{P};

use super::{Amount, PluginResult, Specifier};
use super::utility::{SaveEmitter, ToError, TransactionParser};

//================================================
// Macros
//================================================

// from! _________________________________________

/// Implements `From` for the supplied type on `&Match`.
macro_rules! from {
    ($variant:ident, $ty:ty) => {
        impl<'a> From<&'a Match> for $ty {
            fn from(match_: &'a Match) -> $ty {
                match *match_ {
                    Match::$variant(ref value) => value.clone(),
                    _ => panic!("expected `Match::{}`", stringify!($variant)),
                }
            }
        }
    };
}

//================================================
// Enums
//================================================

// Match _________________________________________

/// A plugin argument that has been matched with a named specifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Match {
    /// An attribute (e.g., `#[cfg(target_os = "windows")]`).
    Attr(Attribute),
    /// A binary operator (e.g., `+`, `*`).
    BinOp(Spanned<BinOpToken>),
    /// A brace-delimited sequence of statements (e.g., `{ log(error, "hi"); return 12; }`).
    Block(P<Block>),
    /// A delimited sequence of token trees (e.g., `()`, `[foo - "bar"]`).
    Delim(Spanned<Rc<Delimited>>),
    /// An expression (e.g., `2 + 2`, `if true { 1 } else { 2 }`, `f(42)`).
    Expr(P<Expr>),
    /// An identifier (e.g., `x`, `foo`).
    Ident(Spanned<Ident>),
    /// An item (e.g., `fn foo() { }`, `struct Bar;`).
    Item(P<Item>),
    /// A lifetime (e.g., `'a`).
    Lftm(Spanned<Name>),
    /// A literal (e.g., `322`, `'a'`, `"foo"`).
    Lit(Lit),
    /// A "meta" item, as found in attributes (e.g., `cfg(target_os = "windows")`).
    Meta(P<MetaItem>),
    /// A pattern (e.g., `Some(t)`, `(17, 'a')`, `_`).
    Pat(P<Pat>),
    /// A qualified name (e.g., `T::SpecialA`).
    Path(Path),
    /// A single statement (e.g., `let x = 3`).
    Stmt(Stmt),
    /// A type (e.g., `i32`, `Vec<(char, String)>`, `&T`).
    Ty(P<Ty>),
    /// A single token.
    Tok(Spanned<Token>),
    /// A single token tree.
    Tt(TokenTree),
    /// A sequence which may either contain sequence matches or subsequences.
    Sequence(Vec<Match>),
    /// A count of named sequence repetitions.
    NamedSequence(Spanned<usize>),
}

impl Match {
    //- Accessors --------------------------------

    /// Converts this `Match` to the supplied type.
    ///
    /// # Panics
    ///
    /// * this `Match` cannot be converted to the supplied type
    #[cfg_attr(feature="clippy", allow(needless_lifetimes))]
    pub fn to<'a, T: From<&'a Match>>(&'a self) -> T {
        self.into()
    }
}

from!(Attr, Attribute);
from!(BinOp, Spanned<BinOpToken>);
from!(Block, P<Block>);
from!(Delim, Spanned<Rc<Delimited>>);
from!(Expr, P<Expr>);
from!(Ident, Spanned<Ident>);
from!(Item, P<Item>);
from!(Lftm, Spanned<Name>);
from!(Lit, Lit);
from!(Meta, P<MetaItem>);
from!(Pat, P<Pat>);
from!(Path, Path);
from!(Stmt, Stmt);
from!(Ty, P<Ty>);
from!(Tok, Spanned<Token>);
from!(Tt, TokenTree);
from!(Sequence, Vec<Match>);

impl<'a> From<&'a Match> for Spanned<usize> {
    fn from(match_: &'a Match) -> Spanned<usize> {
        match *match_ {
            Match::NamedSequence(count) => count,
            _ => unreachable!(),
        }
    }
}

impl<'a> From<&'a Match> for Spanned<bool> {
    fn from(match_: &'a Match) -> Spanned<bool> {
        match *match_ {
            Match::NamedSequence(count) => codemap::respan(count.span, count.node != 0),
            _ => unreachable!(),
        }
    }
}

//================================================
// Structs
//================================================

// ArgumentParser ________________________________

/// Parses arguments according to an argument specification.
struct ArgumentParser<'s> {
    parser: TransactionParser<'s>,
    span: Span,
}

impl<'s> ArgumentParser<'s> {
    //- Constructors -----------------------------

    fn new(session: &'s ParseSess, tts: &'s [TokenTree], span: Span) -> ArgumentParser<'s> {
        ArgumentParser { parser: TransactionParser::new(session, tts.into()), span: span }
    }

    //- Mutators ---------------------------------

    fn expect_token(&mut self) -> PluginResult<Token> {
        match self.parser.bump_and_get() {
            Token::Eof => self.span.to_error("unexpected end of arguments"),
            token => Ok(token),
        }
    }

    fn expect_specific_token(&mut self, token: &Token) -> PluginResult<()> {
        let found = try!(self.expect_token());
        if found.mtwt_eq(token) {
            Ok(())
        } else {
            let message = format!("expected `{}`", Parser::token_to_string(token));
            self.parser.get_last_span().to_error(message)
        }
    }

    /// Parses a sequence and returns the number of occurrences of the sequence.
    fn parse_sequence(
        &mut self,
        amount: Amount,
        separator: Option<&Token>,
        specification: &[Specifier],
        matches: &mut HashMap<String, Match>,
    ) -> PluginResult<usize> {
        // Insert empty sequence matches for each named specifier in the sequence.
        for specifier in specification {
            if let Some(name) = specifier.get_name() {
                matches.insert(name.clone(), Match::Sequence(vec![]));
            }
        }

        let required = amount == Amount::OneOrMore;
        let mut count = 0;

        loop {
            self.parser.save();

            // Check for a separator if expected.
            if let Some(ref separator) = separator {
                if count != 0 && !self.parser.eat(separator) {
                    return Ok(count);
                }
            }

            // Attempt to parse an occurrence of the sequence.
            let mut submatches = HashMap::new();
            match self.parse_args(specification, &mut submatches) {
                Ok(()) => count += 1,
                Err(error) => if count == 0 && required {
                    return Err(error);
                } else {
                    self.parser.rollback();
                    return Ok(count);
                },
            }

            // Append the occurrence matches to the sequence matches.
            for (k, v) in submatches {
                match *matches.entry(k).or_insert_with(|| Match::Sequence(vec![])) {
                    Match::Sequence(ref mut sequence) => sequence.push(v),
                    _ => unreachable!(),
                }
            }

            if amount == Amount::ZeroOrOne {
                return Ok(count);
            }
        }
    }

   /// Parses and returns a delimited sequence of token trees.
   fn parse_delim(&mut self) -> PluginResult<Rc<Delimited>> {
        // Check for an open delimiter.
        let (delimiter, open) = match try!(self.expect_token()) {
            Token::OpenDelim(delimiter) => (delimiter, self.parser.get_last_span()),
            invalid => {
                let string = Parser::token_to_string(&invalid);
                let error = format!("expected opening delimiter, found `{}`", string);
                return self.parser.get_last_span().to_error(error);
            },
        };

        // Parse token trees until a matching close delimiter is encountered.
        let tts = self.parser.parse(|p| {
            let sep = SeqSep { sep: None, trailing_sep_allowed: false };
            p.parse_seq_to_end(&Token::CloseDelim(delimiter), sep, |p| p.parse_token_tree())
        });

        let delimited = Delimited {
            delim: delimiter,
            open_span: open,
            tts: try!(tts),
            close_span: self.parser.get_last_span(),
        };
        Ok(Rc::new(delimited))
    }

    #[cfg_attr(feature="clippy", allow(cyclomatic_complexity))]
    fn parse_args(
        &mut self, specification: &[Specifier], matches: &mut HashMap<String, Match>
    ) -> PluginResult<()> {
        macro_rules! insert {
            ($variant:ident, $parse:ident$(.$field:ident)*, $name:expr) => ({
                let match_ = try!(self.parser.$parse($name))$(.$field)*;
                matches.insert($name.clone(), Match::$variant(match_));
            });
        }

        macro_rules! insert_spanned {
            ($variant:ident, $parse:ident$(.$field:ident)*, $name:expr) => ({
                let open = self.parser.get_span();
                let match_ = try!(self.parser.$parse($name))$(.$field)*;
                let spanned = codemap::spanned(open.lo, self.parser.get_last_span().hi, match_);
                matches.insert($name.clone(), Match::$variant(spanned));
            });
        }

        for specifier in specification {
            match *specifier {
                Specifier::Attr(ref name) => insert!(Attr, parse_attribute, name),
                Specifier::BinOp(ref name) => match try!(self.expect_token()) {
                    Token::BinOp(binop) | Token::BinOpEq(binop) => {
                        let spanned = codemap::respan(self.parser.get_last_span(), binop);
                        matches.insert(name.clone(), Match::BinOp(spanned));
                    },
                    _ => {
                        let error = format!("expected binop: '{}'", name);
                        return self.parser.get_last_span().to_error(error);
                    },
                },
                Specifier::Block(ref name) => insert!(Block, parse_block, name),
                Specifier::Delim(ref name) => {
                    let open = self.parser.get_span();
                    let delim = try!(self.parse_delim());
                    let spanned = codemap::spanned(open.lo, delim.close_span.hi, delim);
                    matches.insert(name.clone(), Match::Delim(spanned));
                },
                Specifier::Expr(ref name) => insert!(Expr, parse_expr, name),
                Specifier::Ident(ref name) => insert_spanned!(Ident, parse_ident, name),
                Specifier::Item(ref name) => insert!(Item, parse_item, name),
                Specifier::Lftm(ref name) => insert_spanned!(Lftm, parse_lifetime.name, name),
                Specifier::Lit(ref name) => insert!(Lit, parse_lit, name),
                Specifier::Meta(ref name) => {
                    let meta = try!(self.parser.parse_meta_item(name)).map(|mut m| {
                        m.span.hi = self.parser.get_last_span().hi;
                        m
                    });
                    matches.insert(name.clone(), Match::Meta(meta));
                },
                Specifier::Pat(ref name) => insert!(Pat, parse_pat, name),
                Specifier::Path(ref name) => insert!(Path, parse_path, name),
                Specifier::Stmt(ref name) => insert!(Stmt, parse_stmt, name),
                Specifier::Ty(ref name) => insert!(Ty, parse_ty, name),
                Specifier::Tok(ref name) => {
                    let tok = try!(self.expect_token());
                    let spanned = codemap::respan(self.parser.get_last_span(), tok);
                    matches.insert(name.clone(), Match::Tok(spanned));
                },
                Specifier::Tt(ref name) => insert!(Tt, parse_token_tree, name),
                Specifier::Specific(ref expected) => try!(self.expect_specific_token(expected)),
                Specifier::Delimited(delimiter, ref specification) => {
                    try!(self.expect_specific_token(&Token::OpenDelim(delimiter)));
                    try!(self.parse_args(&specification, matches));
                    try!(self.expect_specific_token(&Token::CloseDelim(delimiter)));
                },
                Specifier::Sequence(amount, ref separator, ref specification) => {
                    try!(self.parse_sequence(amount, separator.as_ref(), specification, matches));
                },
                Specifier::NamedSequence(ref name, amount, ref separator, ref specification) => {
                    let open = self.parser.get_last_span();
                    let separator = separator.as_ref();
                    let count = self.parse_sequence(amount, separator, specification, matches);
                    let close = self.parser.get_last_span();
                    let spanned = codemap::spanned(open.lo, close.hi, try!(count));
                    matches.insert(name.clone(), Match::NamedSequence(spanned));
                },
            }
        }

        Ok(())
    }

    pub fn parse(&mut self, specification: &[Specifier]) -> PluginResult<HashMap<String, Match>> {
        let mut matches = HashMap::new();
        try!(self.parse_args(specification, &mut matches));
        if self.parser.is_empty() {
            Ok(matches)
        } else {
            let start = self.parser.get_span();
            let span = Span { lo: start.lo, hi: self.span.hi, expn_id: self.span.expn_id };
            span.to_error("too many arguments")
        }
    }
}

//================================================
// Functions
//================================================

/// Parses the supplied arguments with the supplied specification.
pub fn parse_args(
    session: &ParseSess, tts: &[TokenTree], specification: &[Specifier]
) -> PluginResult<HashMap<String, Match>> {
    if tts.is_empty() && specification.is_empty() {
        return Ok(HashMap::new());
    }

    // Build a span that spans all the arguments.
    let start = tts.iter().nth(0).map_or(DUMMY_SP, |s| s.get_span());
    let end = tts.iter().last().map_or(DUMMY_SP, |s| s.get_span());
    let span = Span { lo: start.lo, hi: end.hi, expn_id: start.expn_id };

    if !tts.is_empty() && specification.is_empty() {
        return span.to_error("too many arguments");
    }

    // Parse the arguments.
    let handler = Handler::with_emitter(false, false, Box::new(SaveEmitter));
    let mut codemap = CodeMap::new();
    codemap.files = session.codemap().files.clone();
    let session = ParseSess::with_span_handler(handler, Rc::new(codemap));
    ArgumentParser::new(&session, tts, span).parse(specification)
}
