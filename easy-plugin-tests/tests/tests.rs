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

#![cfg_attr(not(feature="syntex"), feature(plugin, plugin_registrar, rustc_private))]

#![cfg_attr(not(feature="syntex"), allow(plugin_as_library))]

#![cfg_attr(not(feature="syntex"), plugin(easy_plugin))]

#[cfg(feature="syntex")]
extern crate syntex as rustc_plugin;
#[cfg(feature="syntex")]
extern crate syntex_syntax as syntax;
#[cfg(not(feature="syntex"))]
extern crate rustc_plugin;
#[cfg(not(feature="syntex"))]
extern crate syntax;

#[macro_use]
extern crate easy_plugin;

include!(concat!(env!("OUT_DIR"), "/tests.rs"));
