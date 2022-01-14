//! Interpreter context for building verification conditions.
//!

use crate::types::SMTType;

pub struct Var {
    pub name: String,
    pub ty: SMTType,
}

pub struct Context {
    quantified_vars: Vec<Var>,
}
