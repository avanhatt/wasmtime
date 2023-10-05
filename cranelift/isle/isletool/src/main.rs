use clap::Parser;
use cranelift_isle::error::Errors;
use std::path::PathBuf;

#[derive(Parser)]
struct Opts {
    /// The input ISLE DSL source files.
    #[clap(required = true)]
    inputs: Vec<PathBuf>,
}

fn main() -> Result<(), Errors> {
    env_logger::init();

    let opts = Opts::parse();
    let lexer = cranelift_isle::lexer::Lexer::from_files(opts.inputs)?;
    let defs = cranelift_isle::parser::parse(lexer)?;
    let mut typeenv = cranelift_isle::sema::TypeEnv::from_ast(&defs)?;
    let termenv = cranelift_isle::sema::TermEnv::from_ast(&mut typeenv, &defs, true)?;

    for term in termenv.terms {
        println!("term: {:?}", term);
    }

    Ok(())
}
