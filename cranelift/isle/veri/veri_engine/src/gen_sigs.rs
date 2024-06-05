use cranelift_codegen_meta as meta;
use std::env;
use std::process;

fn main() {
    let out_dir = env::var("OUT_DIR").expect("The OUT_DIR environment variable must be set");

    // ISA: x64 for now.
    let isa = meta::isa::Isa::from_arch("x86_64").unwrap();
    println!("isa = {}", isa);
    let isas = vec![isa];

    // Generate.
    let isle_dir = std::path::Path::new(&out_dir);
    if let Err(err) = meta::generate(&isas, &out_dir, isle_dir.to_str().unwrap()) {
        eprintln!("Error: {}", err);
        process::exit(1);
    }
}
