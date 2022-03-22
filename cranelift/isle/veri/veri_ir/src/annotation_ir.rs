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
    // TODO: special case this for function bound vars?
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
    pub sig: TermSignature,
    pub assertions: Vec<Box<Expr>>,
}

impl TermAnnotation {
    /// New annotation
    pub fn new(sig: TermSignature, assertions: Vec<Box<Expr>>) -> Self {
        TermAnnotation { sig, assertions }
    }

    pub fn sig(&self) -> &TermSignature {
        &self.sig
    }

    pub fn assertions(&self) -> &Vec<Box<Expr>> {
        &self.assertions
    }
}

/// Function type with argument and return types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionType {
    pub args: Vec<Type>,
    pub ret: Box<Type>,
}

/// Higher-level type, not including bitwidths.
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

/// Type-specified constants
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
    pub args: Vec<BoundVar>,
    pub body: Box<Expr>,
}

/// Application of a function expression to arguments
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionApplication {
    pub func: Box<Expr>,
    pub args: Vec<Box<Expr>>,
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
    //      Note: these follow the naming conventions of the SMT theory of bitvectors:
    //      https://smtlib.cs.uiowa.edu/version1/logics/QF_BV.smt
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

    // A special, high level conversion to a destination width. This currently
    // assumes that the source width is the LHS values BV width.
    BVConvTo(usize, Box<Expr>),
    // A special, high level conversion from a source width. This currently
    // assumes that the destination width is the LHS values BV width.
    BVConvFrom(usize, Box<Expr>),

    Function(Function),
    FunctionApplication(FunctionApplication),
    List(Vec<Box<Expr>>),
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

pub fn isle_annotation_for_term(term: &str) -> Option<TermAnnotation> {
    match term {
        // (spec (sig (args (x: bvX) (ret: bvX))
        //       (assumptions (= x ret)))
        "lower" | "put_in_reg" | "value_reg" | "first_result" | "inst_data" => {
            // No-op for now
            let arg = BoundVar::new("arg");
            let result = BoundVar::new("ret");
            let identity = Expr::binary(Expr::Eq, arg.as_expr(), result.as_expr());
            let func = TermSignature {
                args: vec![arg],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![Box::new(identity)]))
        }
        "InstructionData.Binary" => {
            // List must have length 2 since it's a Binary
            let list_ty = Type::BitVectorList(2);
            let arg_list = BoundVar::new("arg_list");
            let result = BoundVar::new("ret");

            let opcode = BoundVar::new_with_ty(
                "opcode",
                &Type::Function(FunctionType {
                    args: vec![list_ty],
                    ret: Box::new(Type::BitVector),
                }),
            );

            let app = Expr::FunctionApplication(FunctionApplication {
                func: Box::new(opcode.as_expr()),
                args: vec![Box::new(Expr::Var(arg_list.name.clone()))],
            });
            let eq = Expr::binary(Expr::Eq, app, result.as_expr());

            let func = TermSignature {
                args: vec![opcode, arg_list],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![Box::new(eq)]))
        }
        "value_type" => {
            let arg = BoundVar::new("arg");
            let result = BoundVar::new("ret");
            let ty_eq = Expr::binary(Expr::Eq, arg.as_expr(), Expr::TyWidth);
            let func = TermSignature {
                args: vec![arg],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![Box::new(ty_eq)]))
        }
        "value_array_2" => {
            let arg1 = BoundVar::new("arg1");
            let arg2 = BoundVar::new("arg2");
            let result = BoundVar::new("ret");

            let ls = Expr::List(vec![Box::new(Expr::Var(arg1.name.clone())),
                Box::new(Expr::Var(arg2.name.clone()))]);
            let eq = Expr::binary(Expr::Eq, ls, result.as_expr());

            let func = TermSignature {
                args: vec![arg1, arg2],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![Box::new(eq)]))
        }
        // (spec (sig (args x: bvX) (ret: bvX))
        //       (assumptions (= x ret)))
        "has_type" => {
            // Add an assertion on the type
            let ty_arg = BoundVar::new("ty");
            let arg = BoundVar::new("arg");
            let result = BoundVar::new("ret");
            let ty_eq = Expr::binary(Expr::Eq, ty_arg.as_expr(), Expr::TyWidth);
            let identity = Expr::binary(Expr::Eq, arg.as_expr(), result.as_expr());
            let func = TermSignature {
                args: vec![ty_arg, arg],
                ret: result,
            };
            Some(TermAnnotation::new(func, 
                vec![Box::new(ty_eq), Box::new(identity)]))
        }
        "fits_in_64" => {
            // Identity, but add assertion on type
            let arg = BoundVar::new("arg");
            let result = BoundVar::new("ret");
            let identity = Expr::binary(Expr::Eq, arg.as_expr(), result.as_expr());
            let ty_fits = Expr::binary(
                Expr::Lte,
                arg.as_expr(),
                Expr::Const(Const {
                    ty: Type::Int,
                    value: 64_i128,
                }),
            );
            let func = TermSignature {
                args: vec![arg],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![Box::new(identity), Box::new(ty_fits)]))
        }
        "iadd" => {
            let a = BoundVar::new("a");
            let b = BoundVar::new("b");
            let r = BoundVar::new("r");
            let sem = Expr::binary(
                Expr::Eq,
                Expr::binary(Expr::BVAdd, a.as_expr(), b.as_expr()),
                r.as_expr(),
            );
            let func = TermSignature {
                args: vec![a, b],
                ret: r,
            };
            Some(TermAnnotation::new(func, vec![Box::new(sem)]))
        }
        "Opcode.Iadd" => {
            let value_list = BoundVar::new("xs");
            let r = BoundVar::new("r");
            let x = Expr::GetElement(Box::new(value_list.as_expr()), 0);
            let y = Expr::GetElement(Box::new(value_list.as_expr()), 1);
            let body = Expr::binary(Expr::BVAdd, x, y);
            let func_expr = Expr::Function(Function {
                name: "Opcode.Iadd".to_string(),
                args: vec![value_list],
                ty: Type::Function(FunctionType {
                    args: vec![Type::BitVectorList(2)],
                    ret: Box::new(Type::BitVector),
                }),
                body: Box::new(body),
            });
            let body_semantics = Expr::binary(Expr::Eq, r.as_expr(), func_expr);
            // The opcode itself takes no arguments
            let func = TermSignature {
                args: vec![],
                ret: r,
            };
            Some(TermAnnotation::new(func, vec![Box::new(body_semantics)]))
        }
        "add" => {
            let t = BoundVar::new("ty");
            let a = BoundVar::new("a");
            let b = BoundVar::new("b");
            let r = BoundVar::new("r");
            let sem = Expr::binary(
                Expr::Eq,
                Expr::binary(Expr::BVAdd, a.as_expr(), b.as_expr()),
                r.as_expr(),
            );
            let func = TermSignature {
                args: vec![t, a, b],
                ret: r,
            };
            Some(TermAnnotation::new(func, vec![Box::new(sem)]))
        }
        "imm12_from_negated_value" => {
            // Width: bv12
            let imm_arg = BoundVar::new("imm_arg");

            // Width: bvX
            let result = BoundVar::new("ret");

            // Negate and convert
            let as_ty = Expr::BVConvFrom(12, Box::new(imm_arg.as_expr()));
            let res = Expr::unary(Expr::BVNeg, as_ty);
            let eq = Expr::binary(Expr::Eq, res, result.as_expr());
            let sig = TermSignature {
                args: vec![imm_arg],
                ret: result,
            };
            Some(TermAnnotation::new(sig, vec![Box::new(eq)]))
        }
        "sub_imm" => {
            // Declare bound variables
            let ty_arg = BoundVar::new("ty");
            let reg_arg = BoundVar::new("reg");
            let result = BoundVar::new("ret");

            // Width: bv12
            let imm_arg = BoundVar::new("imm_arg");

            // Conversion step
            let as_ty = Expr::BVConvFrom(12, Box::new(imm_arg.as_expr()));
            let res = Expr::binary(Expr::BVSub, reg_arg.as_expr(), as_ty);
            let assertion = Expr::binary(Expr::Eq, res, result.as_expr());
            let func = TermSignature {
                args: vec![ty_arg, reg_arg, imm_arg],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![Box::new(assertion)]))
        }
        _ => None,
    }
}
