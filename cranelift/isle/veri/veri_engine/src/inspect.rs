use cranelift_isle as isle;
use isle::compile::create_envs;
use std::path::PathBuf;

pub fn inspect_rules(inputs: Vec<PathBuf>) {
    let lexer = isle::lexer::Lexer::from_files(&inputs).unwrap();

    // Parses to an AST, as a list of definitions
    let defs = isle::parser::parse(lexer).expect("should parse");

    // Produces environments including terms, rules, and maps from symbols and
    // names to types
    let (typeenv, termenv) = create_envs(&defs).unwrap();

    // // Parse annotations.
    // let annotation_env = parse_annotations(&defs, &termenv, &typeenv);

    // Dump all rules.
    for rule in termenv.rules {
        // Rule name.
        let name = match rule.name {
            Some(name) => typeenv.syms[name.index()].clone(),
            None => format!("{:?}", rule.id),
        };

        // Rule term.
        let lhs_term = &termenv.terms[rule.root_term.index()];
        let lhs_name = typeenv.syms[lhs_term.name.index()].clone();

        // Report.
        println!("rule: {}", name);
        println!("\tlhs_name: {}", lhs_name);
    }
}
