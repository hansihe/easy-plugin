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

use syntax::ast::*;
use syntax::codemap::{Span, Spanned};
use syntax::tokenstream::{TokenTree};

use super::{PluginResult};

//================================================
// Macros
//================================================

// to_error! _____________________________________

/// Defines a `ToError` implementation for the supplied type.
macro_rules! to_error {
    ($ty:ty) => (
        impl<T, S: Into<String>> ToError<T, S> for $ty {
            fn to_error(&self, message: S) -> PluginResult<T> {
                Err((self.span, message.into()))
            }
        }
    );
}

//================================================
// Traits
//================================================

// PluginResultExt _______________________________

/// Extends `PluginResult<T>`.
pub trait PluginResultExt<T> {
    /// Returns this `PluginResult<T>` with a different span if it is an `Err`.
    fn map_err_span(self, span: Span) -> PluginResult<T>;

    /// Returns this `PluginResult<T>` with a different message if it is an `Err`.
    fn map_err_message<S: Into<String>>(self, message: S) -> PluginResult<T>;
}

impl<T> PluginResultExt<T> for PluginResult<T> {
    fn map_err_span(self, span: Span) -> PluginResult<T> {
        self.map_err(|(_, m)| (span, m))
    }

    fn map_err_message<S: Into<String>>(self, message: S) -> PluginResult<T> {
        self.map_err(|(s, _)| (s, message.into()))
    }
}

// ToError _______________________________________

/// A type that can be extended into a `PluginResult<T>`.
pub trait ToError<T, S> where S: Into<String> {
    /// Returns an `Err` value with the span of this value and the supplied message.
    fn to_error(&self, message: S) -> PluginResult<T>;
}

impl<T, S: Into<String>> ToError<T, S> for Span {
    fn to_error(&self, message: S) -> PluginResult<T> {
        Err((*self, message.into()))
    }
}

impl<T, S: Into<String>> ToError<T, S> for TokenTree {
    fn to_error(&self, message: S) -> PluginResult<T> {
        Err((self.get_span(), message.into()))
    }
}

impl<T, U, S: Into<String>> ToError<T, S> for Spanned<U> {
    fn to_error(&self, message: S) -> PluginResult<T> {
        Err((self.span, message.into()))
    }
}

to_error!(Block);
to_error!(Expr);
to_error!(Item);
to_error!(Pat);
to_error!(Path);
to_error!(Stmt);
to_error!(Ty);
