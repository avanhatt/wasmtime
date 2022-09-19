//! Verification Intermediate Representation for relevant types, eventually to
//! be lowered to SMT. The goal is to leave some freedom to change term
//! encodings or the specific solver backend.
//! 
//! Note: annotations use the higher-level IR in annotation_ir.rs.
pub mod annotation_ir;
pub mod isle_annotations;

use std::collections::HashMap;

/// Packaged semantics for a single rule, included metadata on which terms
/// are not yet defined.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleSemantics {
    pub lhs: Expr,
    pub rhs: Expr,

    pub quantified_vars: Vec<String>,
    pub assumptions: Vec<Expr>,
    //  TODO: sanity check uniqueness
    pub lhs_undefined_terms: Vec<UndefinedTerm>,
    pub rhs_undefined_terms: Vec<UndefinedTerm>,
}
// TODO: can nuke this
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RulePath {
    pub rules: Vec<RuleSemantics>,
    pub undefined_term_pairs: Vec<(UndefinedTerm, UndefinedTerm)>,
}

/// A structure linking rules that share intermediate terms. A path from a root
/// RuleSemantics to a leaf of the tree represents a valid rewriting if all
/// assumptions along the path are feasible.
#[derive(Clone, Debug)]
pub struct RuleTree {
    pub value: RuleSemantics,
    // maybe want an RC cell instead of a Box
    pub children: HashMap<BoundVar, Vec<RuleTree>>,
    pub height: usize,
}

/// Verification IR annotations for an ISLE term consist of the function
/// signature and a list of assertions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VIRTermAnnotation {
    pub sig: VIRTermSignature,
    pub assertions: Vec<Expr>,
}

impl VIRTermAnnotation {
    /// New annotation, ensuring that each assertions is a bool.
    pub fn new(sig: VIRTermSignature, assertions: Vec<Expr>) -> Self {
        // assert!(assertions.iter().all(|a| a.ty().is_bool()));
        VIRTermAnnotation { sig, assertions }
    }

    pub fn func(&self) -> &VIRTermSignature {
        &self.sig
    }

    pub fn assertions(&self) -> &Vec<Expr> {
        &self.assertions
    }
}
/// A function signature annotation, including the bound variable names for all
/// arguments and the return value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VIRTermSignature {
    pub args: Vec<BoundVar>,
    pub ret: BoundVar,
}
/// A bound function with named arguments, the VIR type signature, and the body
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    pub ty: Type,
    pub args: Vec<BoundVar>,
    pub body: Box<Expr>,
}

/// Application of a function expression to arguments
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionApplication {
    pub ty: Type,
    pub func: Box<Expr>,
    pub args: Vec<Expr>,
}
/// A bound variable, including the VIR type
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoundVar {
    pub name: String,
    pub ty: Type,
}

impl BoundVar {
    /// Construct a new bound variable, cloning from references
    pub fn new(name: &str, ty: &Type) -> Self {
        BoundVar {
            name: name.to_string(),
            ty: ty.clone(),
        }
    }
}

/// An ISLE term that does not yet have a defined semantics (that is, a
/// term that has no annotation). 
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UndefinedTerm {
    pub name: String,
    pub ret: BoundVar,
    pub args: Vec<Expr>,
}

/// Verification type
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    /// The expression is a bitvector, currently modeled in the
    /// logic QF_BV https://smtlib.cs.uiowa.edu/version1/logics/QF_BV.smt
    /// This corresponds to Cranelift's Isle type:
    /// (type Value (primitive Value))
    BitVector,

    /// The expression is a boolean. This does not directly correspond
    /// to a specific Cranelift Isle type, rather, we use it for the
    /// language of assertions.
    Bool,

    /// The expression is an Isle type. This is separate from BitVector
    /// because it allows us to use a different solver type (e.h., Int)
    //. for assertions (e.g., fits_in_64).
    /// This corresponds to Cranelift's Isle type:
    /// (type Type (primitive Type))
    Int,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Terminal {
    Var(String),
    Const(i128),
    True,
    False,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    // Boolean operations
    Not, 

    // Bitvector operations
    BVNeg,
    BVNot,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    // Boolean operations
    And,
    Or,
    Imp, 
    Eq, 
    Lte,

    // Bitvector operations
    BVAdd,
    BVSub,
    BVAnd,
    BVOr,
    BVRotl,
    BVShl,
    BVShr,
}


/// Expressions (combined across all types).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    // Terminal nodes
    Terminal(Terminal),

    // Opcode nodes
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),

    // Conversions
    BVZeroExt(usize, Box<Expr>),
    BVSignExt(usize, Box<Expr>),
    BVExtract(usize, usize, Box<Expr>),
    BVIntToBV(Box<Expr>),

    // Undefined terms
    UndefinedTerm(UndefinedTerm)
}

// impl VIRType {
//     pub fn eq(x: Expr, y: Expr) -> Expr {
//         assert_eq!(x.ty(), y.ty(), "(= {:?} {:?})", x, y);
//         Expr::Eq(Box::new(x), Box::new(y))
//     }

//     pub fn bv_const(&self, x: i128) -> Expr {
//         Expr::Const(self.clone(), x)
//     }

//     pub fn bv_var(&self, s: String) -> Expr {
//         Expr::Var(BoundVar {
//             name: s,
//             ty: self.clone(),
//         })
//     }

//     pub fn width(&self) -> usize {
//         match *self {
//             Self::BitVector(s) => s,
//             _ => unreachable!("Unexpected type: {:?}", self),
//         }
//     }

//     pub fn is_bv(&self) -> bool {
//         matches!(*self, Self::BitVector(..))
//     }

//     pub fn is_bool(&self) -> bool {
//         matches!(*self, Self::Bool)
//     }

//     pub fn is_int(&self) -> bool {
//         matches!(*self, Self::Int)
//     }
// }

pub fn all_starting_bitvectors() -> Vec<usize> {
    vec![
        // VIRType::BitVector(1),
        // VIRType::BitVector(8),
        // VIRType::BitVector(16),
        // VIRType::BitVector(32),
        // VIRType::BitVector(64),
        // VIRType::BitVector(128),
    ]
}

impl BoundVar {
    pub fn as_expr(&self) -> Expr {
        Expr::Terminal(Terminal::Var(self.name.clone()))
    }
}

/// To-be-flushed-out verification counterexample for failures
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample {}

/// To-be-flushed-out verification result
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerificationResult {
    InapplicableRule,
    Success,
    Failure(Counterexample),
    Unknown,
}
