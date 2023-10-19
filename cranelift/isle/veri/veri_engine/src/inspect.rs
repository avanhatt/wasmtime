use cranelift_isle as isle;
use isle::compile::create_envs;
use isle::sema::{Expr, Pattern, Rule, TermEnv, TermId, TypeEnv};
use std::collections::HashSet;
use std::path::PathBuf;

fn pattern_terms(pattern: &Pattern) -> HashSet<TermId> {
    // TODO: implement with PatternVisitor?
    match pattern {
        Pattern::BindPattern(_, _, ref subpat) => pattern_terms(subpat),
        Pattern::Term(_, term, ref args) => {
            let mut terms = HashSet::new();
            terms.insert(term.clone());
            for arg in args {
                terms.extend(pattern_terms(arg));
            }
            terms
        }
        Pattern::And(_, ref children) => {
            let mut terms = HashSet::new();
            for child in children {
                terms.extend(pattern_terms(child));
            }
            terms
        }
        _ => HashSet::new(),
    }
}

fn rule_root_pattern(rule: &Rule, termenv: &TermEnv) -> Pattern {
    // TODO: is ret_ty the right type to report here?
    let term = &termenv.terms[rule.root_term.index()];
    Pattern::Term(term.ret_ty, term.id, rule.args.clone())
}

fn rule_terms(rule: &Rule, termenv: &TermEnv) -> HashSet<TermId> {
    let root_pattern = rule_root_pattern(rule, termenv);
    pattern_terms(&root_pattern)
}

fn expr_terms(expr: &Expr) -> HashSet<TermId> {
    // TODO: implement with ExprVisitor?
    match expr {
        Expr::Term(_, term, ref args) => {
            let mut terms = HashSet::new();
            terms.insert(term.clone());
            for arg in args {
                terms.extend(expr_terms(arg));
            }
            terms
        }
        Expr::Let {
            ty: _,
            ref bindings,
            ref body,
        } => {
            let mut terms = HashSet::new();
            for &(_, _, ref var_expr) in bindings {
                terms.extend(expr_terms(var_expr));
            }
            terms.extend(expr_terms(body));
            terms
        }
        _ => HashSet::new(),
    }
}

fn rule_name(rule: &Rule, typeenv: &TypeEnv) -> String {
    match rule.name {
        Some(name) => typeenv.syms[name.index()].clone(),
        None => format!("{:?}", rule.id),
    }
}

fn term_name(term_id: &TermId, typeenv: &TypeEnv, termenv: &TermEnv) -> String {
    let term = &termenv.terms[term_id.index()];
    typeenv.syms[term.name.index()].clone()
}

fn node_name(s: &String) -> String {
    s.replace(".", "_")
}

fn print_graph_cluster(terms: &HashSet<TermId>, typeenv: &TypeEnv, termenv: &TermEnv) {
    print!("{{");
    for term in terms {
        let name = term_name(&term, &typeenv, &termenv);
        print!(" {}", node_name(&name));
    }
    print!(" }}");
}

pub fn inspect_rules(inputs: Vec<PathBuf>) {
    let lexer = isle::lexer::Lexer::from_files(&inputs).unwrap();

    // Parses to an AST, as a list of definitions
    let defs = isle::parser::parse(lexer).expect("should parse");

    // Produces environments including terms, rules, and maps from symbols and
    // names to types
    let (typeenv, termenv) = create_envs(&defs).unwrap();

    // // Parse annotations.
    // let annotation_env = parse_annotations(&defs, &termenv, &typeenv);

    // Dump rules graph.
    println!("digraph isle {{");
    println!("\trankdir=\"LR\"");
    println!("\tnode [fontsize=10, shape=box, height=0.25]");
    for rule in &termenv.rules {
        // Just focus on named rules for now.
        if rule.name.is_none() {
            continue;
        }

        let lhs_terms = rule_terms(&rule, &termenv);
        let rhs_terms = expr_terms(&rule.rhs);

        print!("\t// {}\n\t", rule_name(&rule, &typeenv));
        print_graph_cluster(&lhs_terms, &typeenv, &termenv);
        print!(" -> ");
        print_graph_cluster(&rhs_terms, &typeenv, &termenv);
        print!("\n");
    }
    println!("}}");
}
