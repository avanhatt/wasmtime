//! Prototype verification tool for Cranelift's ISLE lowering rules.

use clap::{Parser, ArgAction};
use std::env;
use std::path::PathBuf;
use veri_engine_lib::verify::verify_rules;

#[derive(Parser)]
#[clap(about, version, author)]
struct Args {
    /// Sets the input file
    #[clap(value_name = "INPUT")]
    input: String,

    /// Which LHS root to verify
    #[clap(short, long, default_value = "lower")]
    term: String,

    /// Don't use the aarch64 and prelude ISLE files
    #[clap(short, long, action=ArgAction::SetTrue)]
    noaarch64: bool,
}

fn main() {
    env_logger::init();

    let cur_dir = env::current_dir().expect("Can't access current working directory");

    let args = Args::parse();
    let mut inputs = vec![];

    dbg!(args.noaarch64);

    if dbg!(!args.noaarch64) {
        print!("HEREEE");
        // TODO: clean up path logic
        inputs.push(cur_dir.join("../../../codegen/src").join("clif_lower.isle"));
        inputs.push(cur_dir.join("../../../codegen/src").join("prelude.isle"));
        inputs.push(
            cur_dir
                .join("../../../codegen/src")
                .join("prelude_lower.isle"),
        );

        // Disable for now to not have to consider all rules
        // inputs.push(cur_dir.join("../../../codegen/src/isa/aarch64").join("inst.isle"));
    }

    inputs.push(PathBuf::from(args.input));
    verify_rules(inputs, args.term)
}
