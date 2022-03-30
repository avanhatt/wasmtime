use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::collections::{HashMap};

use crate::parser::{TermAnnotationParser};
use veri_ir::annotation_ir::{TermAnnotation};

fn get_term(isle: &str) -> &str {
    if !isle.contains("decl") {
        panic!("could not find term in line \"{}\"", isle);
    }

    let tokens: Vec<&str> = isle.split(" ").collect();
    tokens[1]
}

pub struct AnnotationEnv {
    pub annotation_map: HashMap<String, TermAnnotation>,
}

pub fn parse(filename: &str) -> AnnotationEnv {
    let mut reader = get_reader(filename).unwrap();
    let mut line = String::new();

    let mut annotation_env = HashMap::new();
    let p = TermAnnotationParser::new();

    loop {
        let mut cur = String::from("");

        match reader.read_line(&mut line) {
            Ok(bytes_read) => {
                if bytes_read == 0 {
                    break;
                }

                // ignore lines that don't start with ;;@
                if line.len() < 3 || &line[..3] != ";;@" {
                    line.clear();
                    continue;
                }
                
                // lines that begin with ;;@ are part of annotations
                let mut annotation_line = line.clone();
                while annotation_line.len() >= 3 && &annotation_line[..3] == ";;@" {
	            cur = cur + &annotation_line[3..];
                    annotation_line.clear();
                    if let Err(err) = reader.read_line(&mut annotation_line) {
                        panic!("Error reading file: {}", err);
                    }
                }

                let annotation = p.parse(&cur).unwrap();
                cur = String::from("");

                // parse the term associated with the annotation
                let term = get_term(&annotation_line).to_owned();
	        annotation_env.insert(term, annotation);
                line.clear();
            }
            Err(err) => {
                panic!("Error reading file: {}", err);
            }
        }
    }

    AnnotationEnv{annotation_map: annotation_env}
}

fn get_reader<P>(filename: P) -> io::Result<io::BufReader<File>>
where P: AsRef<Path>, {
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file))
}
