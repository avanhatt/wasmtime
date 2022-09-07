use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::Hash;
use std::path::PathBuf;

use cranelift_isle as isle;
use isle::ast::{Decl, Defs};
use isle::compile::create_envs;
use isle::sema::{Sym, TermEnv, TypeEnv, VarId};
use veri_annotation::parser_wrapper::{parse_annotations, AnnotationEnv};
use veri_ir::annotation_ir;

fn main() {
    let cur_dir = env::current_dir().expect("Can't access current working directory");

    // TODO: clean up path logic
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");

    // Disable for now to not have to consider all rules
    // let aarch64_isle = cur_dir.join("../../../codegen/src/isa/aarch64").join("inst.isle");

    let matches = Command::new("Verification Engine for ISLE")
        .arg(
            Arg::new("INPUT")
                .help("Sets the input file")
                .required(true)
                .index(1),
        )
        .get_matches();
    let input = PathBuf::from(matches.value_of("INPUT").unwrap());
    let inputs = vec![clif_isle, prelude_isle, input];

    let (typeenv, termenv) = isle_files_to_terms(&inputs);
    let annotation_env = parse_annotations(&inputs);

    let files = vec!["examples/src/main.rsuextend.isle"];
    let lexer = isle::lexer::Lexer::from_files(&files).unwrap();
    
    let defs = isle::parser::parse(lexer).expect("should parse");
    let decls = build_decl_map(defs);

    for r in &termenv.rules {
        let s = type_annotations_using_rule(r, &annotation_env, &decls, &typeenv, &termenv);
        for a in s.annotation_infos {
            println!("{}", a.term);
            for (var, type_var) in a.var_to_type_var {
                println!("{}: {:#?}", var, s.type_var_to_type[&type_var]);
            }
            println!();
        }
    }

    // For now, verify rules rooted in `lower`
    verify_rules_with_lhs_root("lower", &termenv, &typeenv, &annotation_env);
}