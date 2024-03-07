use aslp::parser;
use clap::Parser as ClapParser;
use std::{fs, path::PathBuf};

#[derive(ClapParser)]
#[command(version, about)]
struct Args {
    /// Input file to be formatted
    file: PathBuf,
}

fn main() {
    let args = Args::parse();
    let src = fs::read_to_string(args.file).unwrap();
    parser::parse(&src);
}
