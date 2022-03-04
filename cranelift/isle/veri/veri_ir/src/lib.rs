//! Verification Intermediate Representation for relevant types, eventually to 
//! be lowered to SMT. The goal is to leave some freedom to change term 
//! encodings or the specific solver backend.

/// Verification IR annotations for an ISLE term consist of the function 
/// signature and a list of assertions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VIRAnnotation {
    func: FunctionAnnotation,
    assertions: Vec<VIRExpr>,
}

impl VIRAnnotation {

    /// New annotation, ensuring that each assertions is a bool.
    pub fn new(func: FunctionAnnotation, assertions: Vec<VIRExpr>) -> Self {
        assert!(assertions.iter().all(|a| a.ty().is_bool()));
        VIRAnnotation {
            func,
            assertions,
        }
    }

    pub fn func(&self) -> &FunctionAnnotation {
        &self.func
    }


    pub fn assertions(&self) -> &Vec<VIRExpr> {
        &self.assertions
    }
}
/// A function signature annotation, including the bound variable names for all
/// arguments and the return value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionAnnotation {
    pub args: Vec<BoundVar>,
    pub ret: BoundVar,
}
/// A bound function, including the VIR type signature
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    pub ty: VIRType, 
    pub args: Vec<BoundVar>,
}

/// A bound variable, including the VIR type
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundVar {
    pub name: String,
    pub ty: VIRType,
}

impl BoundVar {
    /// Construct a new bound variable, cloning from references
    pub fn new(name: &str, ty: &VIRType) -> Self {
        BoundVar { name: name.to_string(), ty: ty.clone() }
    }
}

/// Verification type
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VIRType {
    /// The expression is a bitvector, currently modeled in the
    /// logic QF_BV https://smtlib.cs.uiowa.edu/version1/logics/QF_BV.smt
    /// This corresponds to Cranelift's Isle type: 
    /// (type Value (primitive Value))
    BitVector(usize),

    // The expression is a list of bitvectors (see above)
    // BitVectorList(length, width)
    BitVectorList(usize, usize),

    /// The expression is a function definition. 
    Function(Vec<VIRType>, Box<VIRType>),

    /// The expression is a boolean. This does not directly correspond 
    /// to a specific Cranelift Isle type, rather, we use it for the
    /// language of assertions.
    Bool,

    /// The expression is an Isle type. This is separate from BitVector
    /// because it allows us to use a different solver type (e.h., Int) 
    //. for assertions (e.g., fits_in_64). 
    /// This corresponds to Cranelift's Isle type: 
    /// (type Type (primitive Type))
    IsleType,
}

/// Expressions (combined across all types).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VIRExpr {
    // Terminal nodes
    Var(BoundVar),
    Const(VIRType, i128),
    True,
    False,

    // Boolean operations
    Not(Box<VIRExpr>),
    And(Box<VIRExpr>, Box<VIRExpr>),
    Or(Box<VIRExpr>, Box<VIRExpr>),
    Imp(Box<VIRExpr>, Box<VIRExpr>),
    Eq(Box<VIRExpr>, Box<VIRExpr>),
    Lte(Box<VIRExpr>, Box<VIRExpr>),

    // Bitvector operations
    // Unary operators
    BVNeg(VIRType, Box<VIRExpr>),
    BVNot(VIRType, Box<VIRExpr>),

    // Binary operators
    BVAdd(VIRType, Box<VIRExpr>, Box<VIRExpr>),
    BVSub(VIRType, Box<VIRExpr>, Box<VIRExpr>),
    BVAnd(VIRType, Box<VIRExpr>, Box<VIRExpr>),

    // Conversions
    BVZeroExt(VIRType, usize, Box<VIRExpr>),
    BVSignExt(VIRType, usize, Box<VIRExpr>),
    BVExtract(VIRType, usize, usize, Box<VIRExpr>),

    Function(Function, Box<VIRExpr>),
    FunctionApplication(VIRType, Box<VIRExpr>, Box<VIRExpr>),
    List(VIRType, Vec<VIRExpr>),
    GetElement(VIRType, Box<VIRExpr>, usize),
}

impl VIRExpr {
    pub fn ty(&self) -> &VIRType {
        match &self {
            VIRExpr::Var(bv) => &bv.ty,
            VIRExpr::Const(t, _) => t,
            VIRExpr::BVNeg(t, _) => t,
            VIRExpr::BVNot(t, _) => t,
            VIRExpr::BVAdd(t, _, _) => t,
            VIRExpr::BVSub(t, _, _) => t,
            VIRExpr::BVAnd(t, _, _) => t,
            VIRExpr::BVZeroExt(t, _, _) => t,
            VIRExpr::BVSignExt(t, _, _) => t,
            VIRExpr::BVExtract(t, _, _, _) => t,
            VIRExpr::Function(func, _) => &func.ty,
            VIRExpr::FunctionApplication(t, _, _) => t,
            VIRExpr::List(t, _) => t,
            VIRExpr::GetElement(t, _, _) => t,
            VIRExpr::True 
            | VIRExpr::False 
            | VIRExpr::Not(..)
            | VIRExpr::And(..)
            | VIRExpr::Or(..)
            | VIRExpr::Imp(..)
            | VIRExpr::Eq(..)
            | VIRExpr::Lte(..) => &VIRType::Bool,
        }
    }
}

impl VIRType {
    pub fn eq(x: VIRExpr, y: VIRExpr) -> VIRExpr {
        assert_eq!(x.ty(), y.ty(), "(= {:?} {:?})", x, y);
        VIRExpr::Eq(Box::new(x), Box::new(y))
    }

    pub fn lte(x: VIRExpr, y: VIRExpr) -> VIRExpr {
        assert_eq!(x.ty(), y.ty(), "(<= {:?}{:?})", x, y);
        VIRExpr::Lte(Box::new(x), Box::new(y))
    }

    pub fn apply(&self, func: VIRExpr, args: VIRExpr) -> VIRExpr {
        assert!(matches!(func.ty(), Self::Function(..)));
        VIRExpr::FunctionApplication(self.clone(), Box::new(func), Box::new(args))
    }

    // TODO: type check
    pub fn list(&self, args: Vec<VIRExpr>) -> VIRExpr {
        let length = args.len();
        assert!(args.iter().all(|a| a.ty().width() == self.width()));
        VIRExpr::List(VIRType::BitVectorList(length, self.width()), args)
    }

    pub fn get_element(&self, ls: VIRExpr, i: usize) -> VIRExpr {
        assert!(i < self.list_len());
        VIRExpr::GetElement(self.element_ty(), Box::new(ls), i)
    }

    pub fn element_ty(&self) -> VIRType {
        assert!(self.is_bv_list());
        Self::BitVector(self.width())
    }

    pub fn list_ty(&self, length: usize) -> VIRType {
        assert!(self.is_bv());
        Self::BitVectorList(length, self.width())
    }

    pub fn list_len(&self) -> usize {
        match *self {
            Self::BitVectorList(l, _) => l,
            _ => unreachable!("Unexpected type: {:?}", self),
        }
    }

    pub fn width(&self) -> usize {
        match *self {
            Self::BitVector(s) => s,
            Self::BitVectorList(_, s) => s,
            _ => unreachable!("Unexpected type: {:?}", self),
        }
    }

    pub fn is_bv(&self) -> bool {
        matches!(*self, Self::BitVector(..))
    }

    pub fn is_bv_list(&self) -> bool {
        matches!(*self, Self::BitVectorList(..))
    }

    pub fn is_bool(&self) -> bool {
        matches!(*self, Self::Bool)   
    }

    pub fn is_function(&self) -> bool {
        matches!(*self, Self::Function(..))   
    }

    pub fn function_arg_types(&self) -> Vec<VIRType> {
        match self {
            VIRType::Function(args, _) => args.clone(),
            _ => unreachable!()
        }  
    }

    pub fn function_ret_type(&self) -> VIRType {
        match self {
            VIRType::Function(_, ret) => *ret.clone(),
            _ => unreachable!()
        }  
    }

    pub fn is_isle_type(&self) -> bool {
        matches!(*self, Self::IsleType)   
    }

    pub fn bv_const(&self, x: i128) -> VIRExpr {
        assert!(self.is_bv());
        VIRExpr::Const(self.clone(), x)
    }

    pub fn isle_type_const(&self, x: i128) -> VIRExpr {
        assert!(self.is_isle_type());
        VIRExpr::Const(self.clone(), x)
    }

    pub fn bv_var(&self, s: String) -> VIRExpr {
        VIRExpr::Var(BoundVar{name: s, ty: self.clone()})
    }

    pub fn bv_unary<F: Fn(VIRType, Box<VIRExpr>) -> VIRExpr>(&self, f: F, x: VIRExpr) -> VIRExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        f(self.clone(), Box::new(x))
    }

    pub fn bv_binary<F: Fn(VIRType, Box<VIRExpr>, Box<VIRExpr>) -> VIRExpr>(
        &self,
        f: F,
        x: VIRExpr,
        y: VIRExpr,
    ) -> VIRExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width(), "({:?}, {:?})", x, y);
        assert_eq!(self.width(), y.ty().width(), "({:?}, {:?})", x, y);
        f(self.clone(), Box::new(x), Box::new(y))
    }

    pub fn bv_extend<F: Fn(VIRType, usize, Box<VIRExpr>) -> VIRExpr>(
        &self,
        f: F,
        i: usize,
        x: VIRExpr,
    ) -> VIRExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        let new_width = self.width() + i;
        f(VIRType::BitVector(new_width as usize), i, Box::new(x))
    }

    /// Extract bits from index l to index h
    pub fn bv_extract(&self, l: usize, h: usize, x: VIRExpr) -> VIRExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        assert!(h >= l);
        let new_width = h - l + 1;
        VIRExpr::BVExtract(VIRType::BitVector(new_width as usize), l, h, Box::new(x))
    }
}

pub fn all_starting_bitvectors() -> Vec<VIRType> {
    vec![
        VIRType::BitVector(1),
        VIRType::BitVector(8),
        VIRType::BitVector(16),
        VIRType::BitVector(32),
        VIRType::BitVector(64),
        VIRType::BitVector(128),
    ]
}

impl BoundVar {
    pub fn as_expr(&self)-> VIRExpr {
        VIRExpr::Var(self.clone())
    }
}

/// To-be-flushed-out verification counterexample for failures
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample {
}

/// To-be-flushed-out verification result
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerificationResult {
    InapplicableRule,
    Success,
    Failure(Counterexample),
    Unknown
}