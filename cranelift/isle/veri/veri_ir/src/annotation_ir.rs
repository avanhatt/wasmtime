/// A higher-level annotation IR that does not specify bitvector widths.
/// This allows annotations to be generic over possible types, which
/// corresponds to how ISLE rewrites are written.

/// A bound variable, including the VIR type
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundVar {
    pub name: String,
    pub ty: Option<Type>,
}

impl BoundVar {
    /// Construct a new bound variable, cloning from references
    pub fn new_with_ty(name: &str, ty: &Type) -> Self {
        BoundVar {
            name: name.to_string(),
            ty: Some(ty.clone()),
        }
    }

    /// Construct a new bound variable, cloning from references
    pub fn new(name: &str) -> Self {
        BoundVar {
            name: name.to_string(),
            ty: None,
        }
    }

    /// An expression with the bound variable's name
    pub fn as_expr(&self) -> Expr {
        Expr::Var(self.name.clone())
    }
}

/// A function signature annotation, including the bound variable names for all
/// arguments and the return value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermSignature {
    pub args: Vec<BoundVar>,
    pub ret: BoundVar,
}

/// Verification IR annotations for an ISLE term consist of the function
/// signature and a list of assertions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermAnnotation {
    sig: TermSignature,
    assertions: Vec<Expr>,
}

impl TermAnnotation {
    /// New annotation
    pub fn new(sig: TermSignature, assertions: Vec<Expr>) -> Self {
        TermAnnotation { sig, assertions }
    }

    pub fn sig(&self) -> &TermSignature {
        &self.sig
    }

    pub fn assertions(&self) -> &Vec<Expr> {
        &self.assertions
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionType {
    pub args: Vec<Type>,
    pub ret: Box<Type>,
}

/// H
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    /// The expression is a bitvector, currently modeled in the
    /// logic QF_BV https://smtlib.cs.uiowa.edu/version1/logics/QF_BV.smt
    /// This corresponds to Cranelift's Isle type:
    /// (type Value (primitive Value))
    BitVector,

    // The expression is a list of bitvectors (see above)
    // BitVectorList(length)
    BitVectorList(usize),

    /// The expression is an integer (currently used for ISLE type,
    /// representing bitwidth)
    Int,

    /// The expression is a function definition.
    Function(FunctionType),

    /// The expression is a boolean.
    Bool,
}

/// Width-specified constants
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Const {
    pub ty: Type,
    pub value: i128,
}

/// A bound function with named arguments, the VIR type signature, and the body
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    pub ty: Type,
    pub args: Vec<Expr>,
    pub body: Box<Expr>,
}

/// Application of a function expression to arguments
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionApplication {
    pub func: Box<Expr>,
    pub args: Vec<Expr>,
}

/// Expressions
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    // Terminal nodes
    Var(String),
    Const(Const),
    True,
    False,

    // Special terminal node: the current width
    TyWidth,

    // Boolean operations
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Imp(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Lte(Box<Expr>, Box<Expr>),

    // Bitvector operations
    // Unary operators
    BVNeg(Box<Expr>),
    BVNot(Box<Expr>),

    // Binary operators
    BVAdd(Box<Expr>, Box<Expr>),
    BVSub(Box<Expr>, Box<Expr>),
    BVAnd(Box<Expr>, Box<Expr>),

    // Conversions
    BVZeroExt(usize, Box<Expr>),
    BVSignExt(usize, Box<Expr>),
    BVExtract(usize, usize, Box<Expr>),
    // A special, high level conversion to a destination width
    BVConvTo(usize, Box<Expr>),
    // A special, high level conversion from a source width
    BVConvFrom(usize, Box<Expr>),

    Function(Function),
    FunctionApplication(FunctionApplication),
    List(Vec<Expr>),
    GetElement(Box<Expr>, usize),
}

impl Expr {
    pub fn var(s: &String) -> Expr {
        Expr::Var(s.clone())
    }

    pub fn unary<F: Fn(Box<Expr>) -> Expr>(f: F, x: Expr) -> Expr {
        f(Box::new(x))
    }

    pub fn binary<F: Fn(Box<Expr>, Box<Expr>) -> Expr>(f: F, x: Expr, y: Expr) -> Expr {
        f(Box::new(x), Box::new(y))
    }
}
