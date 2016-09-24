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

extern crate toml;

use std::fs::{File};
use std::io::{Read, Write};

use toml::{Parser, Value};

macro_rules! string {
    ($value:expr) => ($value.as_str().unwrap().to_string());
    ($table:expr, $name:expr) => (string!($table.get($name).unwrap()));
    ($table:expr, $name:expr, $or:expr) => ($table.get($name).map_or_else($or, |v| string!(v)));
}

struct ExtractorSet {
    type_: String,
    enum_: String,
    description: String,
    parameter: (String, String),
    node: String,
    span: String,
    storage: String,
    extractors: Vec<Extractor>,
}

impl ExtractorSet {
    fn new(value: (&String, &Value)) -> ExtractorSet {
        let table = value.1.as_table().unwrap();
        let parameter = string!(table, "parameter");
        let name = &parameter[..parameter.find(':').unwrap()].to_string();
        let extractors = table.get("extractors").unwrap().as_table().unwrap();
        ExtractorSet {
            type_: value.0.clone(),
            enum_: string!(table, "enum"),
            description: string!(table, "description"),
            parameter: (parameter, name.clone()),
            node: string!(table, "node", || format!("{}.node", name)),
            span: string!(table, "span", || format!("{}.span", name)),
            storage: string!(table, "storage"),
            extractors: extractors.iter().map(|e| Extractor::new(&name, e)).collect(),
        }
    }
}

struct Extractor {
    variant: String,
    function: String,
    types: Vec<String>,
}

impl Extractor {
    fn new(parameter: &str, value: (&String, &Value)) -> Extractor {
        let variant = value.0.clone();
        let function = format!("{}_to_{}", parameter, camel_case_to_snake_case(&variant));
        let slice = value.1.as_slice().unwrap();
        let types = slice.iter().map(|v| string!(v)).collect();
        Extractor { variant: variant, function: function, types: types }
    }
}

fn camel_case_to_snake_case(identifier: &str) -> String {
    let mut snake = String::new();
    for c in identifier.chars() {
        if c.is_uppercase() {
            if !snake.is_empty() {
                snake.push('_');
            }
            snake.extend(c.to_lowercase());
        } else {
            snake.push(c);
        }
    }
    snake
}

fn get_extractor_array(extractors: &[ExtractorSet]) -> String {
    let mut array = "#[doc(hidden)]\n".to_string();
    array.push_str("pub const EXTRACTORS: &'static [&'static str] = &[");
    for set in extractors {
        for extractor in &set.extractors {
            array.push_str(&format!("\"{}\", ", extractor.function.replace("_to_", "_")));
        }
    }
    array.push_str("\"tt_delimited\", ");
    array.push_str("\"tt_sequence\", ");
    array.push_str("\"tt_token\"");
    array.push_str("];\n");
    array
}

fn get_exhaustive_function(set: &ExtractorSet) -> String {
    let mut function = "#[allow(dead_code)]\n".to_string();
    function.push_str(&format!("fn {}_exhaustive({}) ", set.parameter.1, set.parameter.0));
    function.push_str(&format!("{{ match {} {{ ", set.node));
    for extractor in &set.extractors {
        if extractor.types.is_empty() {
            function.push_str(&format!("{}::{} => {{ }}, ", set.enum_, extractor.variant));
        } else {
            function.push_str(&format!("{}::{}(..) => {{ }}, ", set.enum_, extractor.variant));
        }
    }
    function.push_str("} }\n");
    function
}

fn get_documentation(set: &ExtractorSet, extractor: &Extractor) -> String {
    match extractor.types.len() {
        0 => format!("Returns `Ok` if the supplied `{}` is `{}::{}`.", set.type_, set.type_, extractor.variant),
        1 => format!("Returns the `{}::{}` value in the supplied `{}`.", set.enum_, extractor.variant, set.type_),
        _ => format!("Returns the `{}::{}` values in the supplied `{}`.", set.enum_, extractor.variant, set.type_),
    }
}

fn get_arm(set: &ExtractorSet, extractor: &Extractor) -> String {
    let mut arm = format!("{}::{}", set.enum_, extractor.variant);
    let (left, right) = if !extractor.types.is_empty() {
        let mut left = vec![];
        let mut right = vec![];
        for (index, type_) in extractor.types.iter().enumerate() {
            let name = ((97 + index) as u8) as char;
            left.push(format!("ref {}", name));
            match &type_[..] {
                "String" => right.push(format!("{}.to_string()", name)),
                "Option<String>" => right.push(format!("{}.map(|n| n.to_string())", name)),
                _ => right.push(format!("{}.clone()", name)),
            }
        }
        (format!("({})", left.join(", ")), right.join(", "))
    } else {
        ("".into(), "".into())
    };
    arm.push_str(&format!("{} => Ok(({})), ", left, right));
    arm
}

fn get_extractor_function(set: &ExtractorSet, extractor: &Extractor) -> String {
    let mut function = format!("/// {}\n", get_documentation(set, extractor));
    let variant = camel_case_to_snake_case(&extractor.variant);
    function.push_str(&format!("pub fn {}_to_{}({}) ", set.parameter.1, variant, set.parameter.0));
    function.push_str(&format!("-> PluginResult<({})> {{ ", extractor.types.join(", ")));
    function.push_str(&format!("match {} {{ ", set.node));
    function.push_str(&get_arm(set, extractor));
    let error = format!("expected `{}::{}` {}", set.enum_, extractor.variant, set.description);
    function.push_str(&format!("_ => Err(({}, \"{}\".into())), ", set.span, error));
    function.push_str("} }\n");
    function
}

fn get_extract_function(extractors: &[ExtractorSet]) -> String {
    let mut extract = "#[doc(hidden)]\n".to_string();
    extract.push_str("pub fn extract(extractor: &str, argument: &Box<Any>) ");
    extract.push_str("-> PluginResult<Box<Any>> { ");
    extract.push_str("match extractor { ");
    for set in extractors {
        for extractor in &set.extractors {
            extract.push_str(&format!("\"{}\" => ", extractor.function.replace("_to_", "_")));
            let argument = format!("argument.downcast_ref::<{}>().unwrap()", set.storage);
            let map = "|a| Box::new(a) as Box<Any>";
            extract.push_str(&format!("{}({}).map({}) ", extractor.function, argument, map));
            extract.push_str(", ");
        }
    }
    extract.push_str("_ => unreachable!(), } }\n");
    extract
}

fn get_extract_storage_function(extractors: &[ExtractorSet]) -> String {
    let mut extract = "#[doc(hidden)]\n".to_string();
    extract.push_str("pub fn get_extract_storage(context: &ExtCtxt, extractor: &str) -> P<Ty> { ");
    extract.push_str("let ty = match extractor { ");
    for set in extractors {
        for extractor in &set.extractors {
            extract.push_str(&format!("\"{}\" => ", extractor.function.replace("_to_", "_")));
            extract.push_str(&format!("\"({})\", ", extractor.types.join(", ")));
        }
    }
    extract.push_str("_ => unreachable!(), }; ");
    extract.push_str("let tts = context.parse_tts(ty.into()); ");
    extract.push_str("context.new_parser_from_tts(&tts).parse_ty().unwrap() }\n");
    extract
}

fn main() {
    let mut file = File::open("extractor.toml").unwrap();
    let mut contents = String::new();
    file.read_to_string(&mut contents).unwrap();

    let toml = Parser::new(&contents).parse().unwrap();
    let extractors = toml.iter().map(ExtractorSet::new).collect::<Vec<_>>();

    let mut source = "".to_string();
    source.push_str(&get_extractor_array(&extractors));
    for set in &extractors {
        source.push_str(&get_exhaustive_function(set));
        for extractor in &set.extractors {
            source.push_str(&get_extractor_function(set, extractor));
        }
    }
    source.push_str(&get_extract_function(&extractors));
    source.push_str(&get_extract_storage_function(&extractors));

    let mut file = File::create(concat!(env!("OUT_DIR"), "/extractor.rs")).unwrap();
    file.write_all(source.as_bytes()).unwrap();
}
