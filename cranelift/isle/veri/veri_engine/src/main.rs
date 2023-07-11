//! Prototype verification tool for Cranelift's ISLE lowering rules.

use clap::{ArgAction, Parser};
use std::env;
use std::path::PathBuf;
use std::process;
use veri_engine_lib::verify::verify_rules;
use veri_engine_lib::Config;

use cranelift_codegen_meta as meta;
use meta::isa::Isa;

#[derive(Parser)]
#[clap(about, version, author)]
struct Args {
    /// Sets the input file
    #[clap(short, long)]
    input: Option<String>,

    /// Which LHS root to verify
    #[clap(short, long, default_value = "lower")]
    term: String,

    /// Which named rule to verify
    #[clap(long)]
    names: Option<Vec<String>>,

    /// Don't use the prelude ISLE files
    #[clap(short, long, action=ArgAction::SetTrue)]
    noprelude: bool,

    /// Include the aarch64 files
    #[clap(short, long, action=ArgAction::SetTrue)]
    aarch64: bool,

    /// Don't check for distinct possible models
    #[clap(long, action=ArgAction::SetTrue)]
    nodistinct: bool,

    /// Allow dynamic widths for the solver query
    #[clap(short, long, action=ArgAction::SetTrue)]
    dynwidths: bool,
}

fn main() {
    env_logger::init();

    let cur_dir = env::current_dir().expect("Can't access current working directory");

    let args = Args::parse();
    let mut inputs = vec![];

    // Build the relevant ISLE prelude using the meta crate
    let out_dir = "isle-tmp";
    let isle_dir = std::path::Path::new(&out_dir);
    std::fs::create_dir_all(isle_dir).expect("Could not create ISLE source directory");

    // For now, build ISLE files for x86 and aarch64
    let isas = vec![Isa::X86, Isa::Arm64];

    if let Err(err) = meta::generate(&isas, &out_dir, isle_dir.to_str().unwrap()) {
        println!("Meta generate error: {}", err);
        process::exit(1);
    }

    let clif_lower_isle = isle_dir.join("clif_lower.isle");
    inputs.push(PathBuf::from(clif_lower_isle));


    if !args.noprelude {
        // TODO: clean up path logic
        inputs.push(cur_dir.join("../../../codegen/src").join("inst_specs.isle"));
        inputs.push(cur_dir.join("../../../codegen/src").join("prelude.isle"));
        inputs.push(
            cur_dir
                .join("../../../codegen/src")
                .join("prelude_lower.isle"),
        );
    }

    if args.aarch64 {
        inputs.push(
            cur_dir
                .join("../../../codegen/src/isa/aarch64")
                .join("inst.isle"),
        );
        inputs.push(
            cur_dir
                .join("../../../codegen/src/isa/aarch64")
                .join("lower.isle"),
        );
        if args.input.is_some() {
            panic!("Cannot specify both input file and aarch64 mode.")
        }
    } else {
        if let Some(i) = args.input {
            inputs.push(PathBuf::from(i));
        } else {
            panic!("Missing input file in non-aarch64 mode");
        }
    }

    let names = if let Some(names) = args.names {
        let mut names = names;
        names.sort();
        names.dedup();
        Some(names)
    } else {
        None
    };

    let config = Config {
        dyn_width: args.dynwidths,
        term: args.term,
        names: names,
        distinct_check: !args.nodistinct,
        custom_verification_condition: None,
        custom_assumptions: None,
    };


    verify_rules(inputs, &config)
}
