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

#[cfg(feature="syntex")]
extern crate syntex;
#[cfg(feature="syntex")]
extern crate synthax;

use std::path::{Path};

#[cfg(feature="syntex")]
fn expand(source: &Path, destination: &Path) {
    synthax::expand(source, destination).unwrap();
}

#[cfg(not(feature="syntex"))]
fn expand(source: &Path, destination: &Path) {
    use std::io::{Read, Write};

    let mut source = std::fs::File::open(source).unwrap();
    let mut contents = String::new();
    source.read_to_string(&mut contents).unwrap();
    let mut destination = std::fs::File::create(destination).unwrap();
    destination.write_all(contents.as_bytes()).unwrap();
}

pub fn main() {
    let files = &["ast", "lib"];
    for file in files {
        let source = Path::new(&format!("src/{}.rs.in", file)).to_path_buf();
        let destination = Path::new(&env!("OUT_DIR")).join(&format!("{}.rs", file));
        expand(&source, &destination);
    }
}
