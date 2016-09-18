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
