#[derive(Debug)]
pub struct Block {
    pub stmts: Vec<Box<Stmt>>,
}

#[derive(Debug)]
pub enum Stmt {
    ConstDecl {
        ty: Type,
        name: String,
        rhs: Expr,
    },
    VarDeclsNoInit {
        ty: Type,
        names: Vec<String>,
    },
    Assign {
        lhs: LExpr,
        rhs: Expr,
    },
    If {
        cond: Expr,
        then_block: Block,
        // TODO(mbm): else if
        else_block: Block,
    },
}

#[derive(Debug)]
pub enum LExpr {
    ArrayIndex { array: Box<LExpr>, index: Box<Expr> },
    Field { x: Box<LExpr>, name: String },
    Var(String),
}

#[derive(Debug)]
pub enum Expr {
    Apply {
        func: Func,
        types: Vec<Box<Expr>>,
        args: Vec<Box<Expr>>,
    },
    ArrayIndex {
        array: Box<Expr>,
        index: Box<Expr>,
    },
    Field {
        x: Box<Expr>,
        name: String,
    },
    Slices {
        x: Box<Expr>,
        slices: Vec<Box<Slice>>,
    },
    Var(String),
    LitInt(String),
    LitBits(String),
}

#[derive(Debug)]
pub enum Slice {
    LowWidth(Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub struct Func {
    pub name: String,
    pub id: usize,
}

#[derive(Debug)]
pub enum Type {
    Bits(Box<Expr>),
}
