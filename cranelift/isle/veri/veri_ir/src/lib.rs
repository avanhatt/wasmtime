//! Verification Intermediate Representation for relevant types, eventually to
//! be lowered to SMT. The goal is to leave some freedom to change term
//! encodings or the specific solver backend.
//!
//! Note: annotations use the higher-level IR in annotation_ir.rs.
pub mod annotation_ir;
pub mod isle_annotations;

use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeContext {
    pub tyvars: HashMap<Expr, u32>,
    pub tymap: HashMap<u32, Type>,
    pub tyvals: HashMap<u32, i128>,
    // map of type var to set index
    pub bv_unknown_width_sets: HashMap<u32, u32>,
}

/// Packaged semantics for a single rule, included metadata on which terms
/// are not yet defined.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleSemantics {
    pub lhs: Expr,
    pub rhs: Expr,

    pub quantified_vars: Vec<BoundVar>,
    pub free_vars: Vec<BoundVar>,
    pub assumptions: Vec<Expr>,

    pub tyctx: TypeContext,
}

// Used for providing concrete inputs to test rule semantics
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteInput {
    // SMTLIB-formatted bitvector literal
    pub literal: String,
    pub ty: Type,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteTest {
    pub termname: String,
    // List of name, bitvector literal, widths
    pub args: Vec<ConcreteInput>,
    pub output: String,
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
    pub tyvar: u32,
}

/// Verification type
#[derive(Clone, Debug, PartialEq, Eq, Hash, Copy)]
pub enum Type {
    /// The expression is a bitvector, currently modeled in the
    /// logic QF_BV https://smtlib.cs.uiowa.edu/version1/logics/QF_BV.smt
    /// This corresponds to Cranelift's Isle type:
    /// (type Value (primitive Value))
    BitVector(Option<usize>),

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

    // Literal SMT value, for testing
    Literal(String),

    // Value, type variable
    Const(i128, u32),
    True,
    False,
    Wildcard(u32),
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
    Lt,

    // Bitvector operations
    BVMul,
    BVUDiv,
    BVAdd,
    BVSub,
    BVAnd,
    BVOr,
    BVXor,
    BVRotl,
    BVRotr,
    BVShl,
    BVShr,
    BVAShr,
}

/// Expressions (combined across all types).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    // Terminal nodes
    Terminal(Terminal),

    // Opcode nodes
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),

    // Count leading zeros
    CLZ(Box<Expr>),
    A64CLZ(Box<Expr>, Box<Expr>),
    CLS(Box<Expr>),
    A64CLS(Box<Expr>, Box<Expr>),
    Rev(Box<Expr>),
    A64Rev(Box<Expr>, Box<Expr>),

    // ITE
    Conditional(Box<Expr>, Box<Expr>, Box<Expr>),

    // Conversions
    // Extract specified bits
    BVExtract(usize, usize, Box<Expr>),

    // Convert integer to bitvector with that value
    BVIntToBV(usize, Box<Expr>),

    // Convert bitvector to integer with that value
    BVToInt(Box<Expr>),

    // Zero extend, with static or dynamic width
    BVZeroExtTo(usize, Box<Expr>),
    BVZeroExtToVarWidth(Box<Expr>, Box<Expr>),

    // Sign extend, with static or dynamic width
    BVSignExtTo(usize, Box<Expr>),
    BVSignExtToVarWidth(Box<Expr>, Box<Expr>),

    // Conversion to wider/narrower bits, without an explicit extend
    BVConvTo(Box<Expr>),
    BVConvToVarWidth(Box<Expr>, Box<Expr>),

    WidthOf(Box<Expr>),
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
