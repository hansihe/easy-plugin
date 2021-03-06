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

//! Parsers used internally by the easy-plugin crate.

#![cfg_attr(not(feature="syntex"), feature(rustc_private))]

#![warn(missing_copy_implementations, missing_debug_implementations, missing_docs)]

#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]
#![cfg_attr(feature="clippy", warn(clippy))]

#[cfg(feature="syntex")]
extern crate syntex_syntax as syntax;
#[cfg(feature="syntex")]
extern crate syntex_errors as rustc_errors;
#[cfg(not(feature="syntex"))]
extern crate syntax;
#[cfg(not(feature="syntex"))]
extern crate rustc_errors as rustc_errors;

mod utility;
pub use utility::{PluginResult};

pub mod arguments;
pub mod extractor;
pub mod specification;
