#[cfg(feature="syntex")]
extern crate easy_plugin;

use std::path::{Path};

#[cfg(feature="syntex")]
fn expand(source: &Path, destination: &Path) {
    easy_plugin::expand(&source, &destination).unwrap();
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
    let files = &["arguments", "convert", "enums", "errors", "specification", "structs"];
    for file in files {
        let source = Path::new(&format!("tests/{}.rs.in", file)).to_path_buf();
        let destination = Path::new(&env!("OUT_DIR")).join(&format!("{}.rs", file));
        expand(&source, &destination);
    }
}
