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

use std::any::{Any};
use std::collections::{HashMap};
use std::rc::{Rc};

use syntax::codemap::{self, DUMMY_SP, CodeMap, Span};
use syntax::parse::{ParseSess};
use syntax::parse::common::{SeqSep};
use syntax::parse::parser::{Parser};
use syntax::parse::token::{Token};
use syntax::tokenstream::{Delimited, TokenTree};

use syntax_errors::{Handler};

use super::convert;
use super::{Amount, PluginResult, Specifier};
use super::utility::{self, SaveEmitter, ToError, TransactionParser};

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

    fn next_token(&mut self) -> Option<Token> {
        match self.parser.bump_and_get() {
            Token::Eof => None,
            token => Some(token),
        }
    }

    fn expect_specific_token(&mut self, token: &Token) -> PluginResult<()> {
        if self.next_token().map_or(false, |t| utility::mtwt_eq(token, &t)) {
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
                matches.insert(name.clone(), Match::new(Vec::<Match>::new()));
            }
        }

        let required = amount == Amount::OneOrMore;
        let mut count = 0;

        loop {
            self.parser.save();

            // Check for a separator if expected.
            if let Some(separator) = separator {
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
                let entry = matches.entry(k).or_insert_with(|| Match::new(Vec::<Match>::new()));
                entry.0.downcast_mut::<Vec<Match>>().unwrap().push(v);
            }

            if amount == Amount::ZeroOrOne {
                return Ok(count);
            }
        }
    }

   /// Parses and returns a delimited sequence of token trees.
   fn parse_delim(&mut self, name: &str) -> PluginResult<Delimited> {
        // Check for an open delimiter.
        let (delimiter, open) = if let Some(Token::OpenDelim(delimiter)) = self.next_token() {
            (delimiter, self.parser.get_last_span())
        } else {
            let error = format!("expected opening delimiter: '{}'", name);
            return self.parser.get_last_span().to_error(error);
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
        Ok(delimited)
    }

    #[cfg_attr(feature="clippy", allow(cyclomatic_complexity))]
    fn parse_args(
        &mut self, specification: &[Specifier], matches: &mut HashMap<String, Match>
    ) -> PluginResult<()> {
        macro_rules! insert {
            ($variant:ident, $parse:ident$(.$field:ident)*, $name:expr) => ({
                let match_ = try!(self.parser.$parse($name))$(.$field)*;
                matches.insert($name.clone(), Match::new(match_));
            });
        }

        macro_rules! insert_spanned {
            ($variant:ident, $parse:ident$(.$field:ident)*, $name:expr) => ({
                let open = self.parser.get_span();
                let match_ = try!(self.parser.$parse($name))$(.$field)*;
                let spanned = codemap::spanned(open.lo, self.parser.get_last_span().hi, match_);
                matches.insert($name.clone(), Match::new(spanned));
            });
        }

        for specifier in specification {
            match *specifier {
                Specifier::Attr(ref name) => insert!(Attr, parse_attribute, name),
                Specifier::BinOp(ref name) => match self.next_token() {
                    Some(Token::BinOp(binop)) | Some(Token::BinOpEq(binop)) => {
                        let spanned = codemap::respan(self.parser.get_last_span(), binop);
                        matches.insert(name.clone(), Match::new(spanned));
                    },
                    _ => {
                        let error = format!("expected binary operator: '{}'", name);
                        return self.parser.get_last_span().to_error(error);
                    },
                },
                Specifier::Block(ref name) => insert!(Block, parse_block, name),
                Specifier::Delim(ref name) => {
                    let open = self.parser.get_span();
                    let delim = try!(self.parse_delim(name));
                    let spanned = codemap::spanned(open.lo, delim.close_span.hi, delim);
                    matches.insert(name.clone(), Match::new(spanned));
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
                    matches.insert(name.clone(), Match::new(meta));
                },
                Specifier::Pat(ref name) => insert!(Pat, parse_pat, name),
                Specifier::Path(ref name) => insert!(Path, parse_path, name),
                Specifier::Stmt(ref name) => insert!(Stmt, parse_stmt, name),
                Specifier::Ty(ref name) => insert!(Ty, parse_ty, name),
                Specifier::Tok(ref name) => if let Some(token) = self.next_token() {
                    let spanned = codemap::respan(self.parser.get_last_span(), token);
                    matches.insert(name.clone(), Match::new(spanned));
                } else {
                    let error = format!("expected token: '{}'", name);
                    return self.parser.get_last_span().to_error(error);
                },
                Specifier::Tt(ref name) => insert!(Tt, parse_token_tree, name),
                Specifier::Convert(ref name, ref subspecifier, ref converter) => {
                    try!(self.parse_args(&[subspecifier[0].clone()], matches));
                    let node = convert::get_converter_val(converter, &*matches.get(name).unwrap().0);
                    matches.insert(name.clone(), Match(try!(node)));
                },
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
                    if amount == Amount::ZeroOrOne {
                        let spanned = codemap::spanned(open.lo, close.hi, try!(count) != 0);
                        matches.insert(name.clone(), Match::new(spanned));
                    } else {
                        let spanned = codemap::spanned(open.lo, close.hi, try!(count));
                        matches.insert(name.clone(), Match::new(spanned));
                    }
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

// Match _________________________________________

/// A plugin argument that has been matched with a named specifier.
#[derive(Debug)]
pub struct Match(Box<Any>);

impl Match {
    //- Constructors -----------------------------

    /// Constructs a new `Match`.
    fn new<T: Any>(value: T) -> Match {
        Match(Box::new(value))
    }

    //- Accessors --------------------------------

    /// Converts this `Match` to the supplied type.
    ///
    /// # Panics
    ///
    /// * this `Match` cannot be converted to the supplied type
    pub fn get<T: Any + Clone>(&self) -> T {
        self.0.downcast_ref::<T>().expect("invalid match").clone()
    }

    /// Converts this `Match` to a slice of matches.
    ///
    /// # Panics
    ///
    /// * this `Match` cannot be converted to a slice of matches
    pub fn get_matches(&self) -> &[Match] {
        &(self.0.downcast_ref::<Vec<Match>>().expect("invalid match"))[..]
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
    let start = tts.get(0).map_or(DUMMY_SP, |s| s.get_span());
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
