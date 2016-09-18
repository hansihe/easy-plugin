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

//! Functions for extracting the values in AST entities.

use std::any::{Any};
use std::rc::{Rc};

use syntax::ast::*;
use syntax::codemap::{self, Span, Spanned};
use syntax::ext::base::{ExtCtxt};
use syntax::ext::quote::rt::{ExtParseUtils};
use syntax::parse::token::{Token};
use syntax::ptr::{P};
use syntax::tokenstream::{Delimited, SequenceRepetition, TokenTree};

use super::{PluginResult};

include!(concat!(env!("OUT_DIR"), "/extractor.rs"));

/// Returns the `TokenTree::Delimited` value in the supplied `TokenTree`.
pub fn tt_to_delimited(tt: &TokenTree) -> PluginResult<Rc<Delimited>> {
    match *tt {
        TokenTree::Delimited(_, ref delimited) => Ok(delimited.clone()),
        _ => Err((tt.span(), "expected `TokenTree::Delimited` token tree".into())),
    }
}

/// Returns the `TokenTree::Sequence` value in the supplied `TokenTree`.
pub fn tt_to_sequence(tt: &TokenTree) -> PluginResult<Rc<SequenceRepetition>> {
    match *tt {
        TokenTree::Sequence(_, ref sequence) => Ok(sequence.clone()),
        _ => Err((tt.span(), "expected `TokenTree::Sequence` token tree".into())),
    }
}

/// Returns the `TokenTree::Token` value in the supplied `TokenTree`.
pub fn tt_to_token(tt: &TokenTree) -> PluginResult<Spanned<Token>> {
    match *tt {
        TokenTree::Token(span, ref token) => Ok(codemap::respan(span, token.clone())),
        _ => Err((tt.span(), "expected `TokenTree::Token` token tree".into())),
    }
}
