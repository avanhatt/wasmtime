//! Interpreter context for building verification conditions.
//!

use crate::types::SMTType;

pub struct Var {
    pub name: String,
    pub ty: SMTType,
}

pub struct Assumption {}

pub struct AssumptionContext {
    pub quantified_vars: Vec<Var>,
    pub assumptions: Vec<Assumption>,
}
