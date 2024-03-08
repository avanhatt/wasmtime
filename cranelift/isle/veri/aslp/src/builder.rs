use crate::ast::{Block, Expr, Func, LExpr, Slice, Stmt, Type};
use crate::raw;

pub fn build(block: &raw::Block) -> anyhow::Result<Block> {
    build_block(&block.nodes)
}

pub fn build_block(nodes: &Vec<Box<raw::Node>>) -> anyhow::Result<Block> {
    let stmts = build_stmts(&nodes)?;
    Ok(Block { stmts })
}

fn build_stmt(node: &raw::Node) -> anyhow::Result<Stmt> {
    let stmt = expect_term(node)?;
    match stmt.name.as_str() {
        "Stmt_ConstDecl" => {
            let (ty, name, rhs) = expect_ternary(stmt)?;
            let ty = build_type(ty)?;
            let name = expect_var(name)?.clone();
            let rhs = build_expr(rhs)?;
            Ok(Stmt::ConstDecl { ty, name, rhs })
        }
        "Stmt_VarDeclsNoInit" => {
            let (ty, vars) = expect_binary(stmt)?;
            let ty = build_type(ty)?;
            let names = expect_vars(vars)?;
            Ok(Stmt::VarDeclsNoInit { ty, names })
        }
        "Stmt_Assign" => {
            let (lhs, rhs) = expect_binary(stmt)?;
            let lhs = build_lexpr(lhs)?;
            let rhs = build_expr(rhs)?;
            Ok(Stmt::Assign { lhs, rhs })
        }
        "Stmt_If" => {
            let (cond, then_block, elifs, else_block) = expect_quaternary(stmt)?;

            let then_block = expect_block(then_block)?;
            let elifs = expect_array(elifs)?;
            let else_block = expect_block(else_block)?;

            let cond = build_expr(cond)?;
            let then_block = build_block(&then_block.nodes)?;
            if !elifs.elements.is_empty() {
                todo!("else if");
            }
            let else_block = build_block(&else_block.nodes)?;

            Ok(Stmt::If {
                cond,
                then_block,
                else_block,
            })
        }
        name => anyhow::bail!("unimplemented statement: {name}"),
    }
}

fn build_stmts(nodes: &Vec<Box<raw::Node>>) -> anyhow::Result<Vec<Box<Stmt>>> {
    let mut stmts = Vec::new();
    for node in nodes {
        stmts.push(Box::new(build_stmt(node)?));
    }
    Ok(stmts)
}

fn build_lexpr(node: &raw::Node) -> anyhow::Result<LExpr> {
    let lexpr = expect_term(node)?;
    match lexpr.name.as_str() {
        "LExpr_Array" => {
            let (array, index) = expect_binary(lexpr)?;
            let array = Box::new(build_lexpr(array)?);
            let index = Box::new(build_expr(index)?);
            Ok(LExpr::ArrayIndex { array, index })
        }
        "LExpr_Field" => {
            let (x, name) = expect_binary(lexpr)?;
            let x = Box::new(build_lexpr(x)?);
            let name = expect_var(name)?.clone();
            Ok(LExpr::Field { x, name })
        }
        "LExpr_Var" => {
            let var = expect_unary(lexpr)?;
            let name = expect_var(var)?;
            Ok(LExpr::Var(name.clone()))
        }
        name => anyhow::bail!("unimplemented lexpr: {name}"),
    }
}

fn build_expr(node: &raw::Node) -> anyhow::Result<Expr> {
    let expr = expect_term(node)?;
    match expr.name.as_str() {
        "Expr_Array" => {
            let (array, index) = expect_binary(expr)?;
            let array = Box::new(build_expr(array)?);
            let index = Box::new(build_expr(index)?);
            Ok(Expr::ArrayIndex { array, index })
        }
        "Expr_Field" => {
            let (x, name) = expect_binary(expr)?;
            let x = Box::new(build_expr(x)?);
            let name = expect_var(name)?.clone();
            Ok(Expr::Field { x, name })
        }
        "Expr_Var" => {
            let var = expect_unary(expr)?;
            let name = expect_var(var)?;
            Ok(Expr::Var(name.clone()))
        }
        "Expr_TApply" => {
            let (func, types, args) = expect_ternary(expr)?;
            let func = expect_func(func)?;
            let types = expect_array(types)?;
            let args = expect_array(args)?;

            let func = Func {
                name: func.name.clone(),
                id: func.id,
            };
            let types = build_exprs(&types.elements)?;
            let args = build_exprs(&args.elements)?;

            Ok(Expr::Apply { func, types, args })
        }
        "Expr_Slices" => {
            let (x, slices) = expect_binary(expr)?;
            let slices = expect_array(slices)?;

            let x = Box::new(build_expr(x)?);
            let slices = build_slices(&slices.elements)?;

            Ok(Expr::Slices { x, slices })
        }
        "Expr_LitInt" => {
            let lit = expect_unary(expr)?;
            let digits = expect_string(lit)?;
            Ok(Expr::LitInt(digits.clone()))
        }
        "Expr_LitBits" => {
            let lit = expect_unary(expr)?;
            let bits = expect_string(lit)?;
            Ok(Expr::LitBits(bits.clone()))
        }
        name => anyhow::bail!("unimplemented expr: {name}"),
    }
}

fn build_exprs(nodes: &Vec<Box<raw::Node>>) -> anyhow::Result<Vec<Box<Expr>>> {
    let mut exprs = Vec::new();
    for node in nodes {
        exprs.push(Box::new(build_expr(node)?));
    }
    Ok(exprs)
}

fn build_slice(node: &raw::Node) -> anyhow::Result<Slice> {
    let slice = expect_term(node)?;
    match slice.name.as_str() {
        "Slice_LoWd" => {
            let (lo, wd) = expect_binary(slice)?;
            let lo = Box::new(build_expr(lo)?);
            let wd = Box::new(build_expr(wd)?);
            Ok(Slice::LowWidth(lo, wd))
        }
        name => anyhow::bail!("unimplemented slice: {name}"),
    }
}

fn build_slices(nodes: &Vec<Box<raw::Node>>) -> anyhow::Result<Vec<Box<Slice>>> {
    let mut slices = Vec::new();
    for node in nodes {
        slices.push(Box::new(build_slice(node)?));
    }
    Ok(slices)
}

fn build_type(node: &raw::Node) -> anyhow::Result<Type> {
    let ty = expect_term(node)?;
    match ty.name.as_str() {
        "Type_Bits" => {
            let w = expect_unary(ty)?;
            let w = Box::new(build_expr(w)?);
            Ok(Type::Bits(w))
        }
        name => anyhow::bail!("unimplemented type: {name}"),
    }
}

fn expect_term(node: &raw::Node) -> anyhow::Result<&raw::Term> {
    match node {
        raw::Node::Term(t) => Ok(t),
        _ => anyhow::bail!("expected term"),
    }
}

fn expect_array(node: &raw::Node) -> anyhow::Result<&raw::Array> {
    match node {
        raw::Node::Array(a) => Ok(a),
        _ => anyhow::bail!("expected array"),
    }
}

fn expect_block(node: &raw::Node) -> anyhow::Result<&raw::Block> {
    match node {
        raw::Node::Block(b) => Ok(b),
        _ => anyhow::bail!("expected block"),
    }
}

fn expect_var(node: &raw::Node) -> anyhow::Result<&String> {
    match node {
        raw::Node::Var(v) => Ok(v),
        _ => anyhow::bail!("expected var"),
    }
}

fn expect_vars(node: &raw::Node) -> anyhow::Result<Vec<String>> {
    let array = expect_array(node)?;
    let mut vars = Vec::new();
    for node in &array.elements {
        vars.push(expect_var(node)?.clone());
    }
    Ok(vars)
}

fn expect_func(node: &raw::Node) -> anyhow::Result<&raw::Func> {
    match node {
        raw::Node::Func(f) => Ok(f),
        _ => anyhow::bail!("expected function name"),
    }
}

fn expect_string(node: &raw::Node) -> anyhow::Result<&String> {
    match node {
        raw::Node::String(s) => Ok(s),
        _ => anyhow::bail!("expected string"),
    }
}

fn expect_unary(term: &raw::Term) -> anyhow::Result<&raw::Node> {
    if term.args.len() != 1 {
        anyhow::bail!("expected unary");
    }
    Ok(&term.args[0])
}

fn expect_binary(term: &raw::Term) -> anyhow::Result<(&raw::Node, &raw::Node)> {
    if term.args.len() != 2 {
        anyhow::bail!("expected binary");
    }
    Ok((&term.args[0], &term.args[1]))
}

fn expect_ternary(term: &raw::Term) -> anyhow::Result<(&raw::Node, &raw::Node, &raw::Node)> {
    if term.args.len() != 3 {
        anyhow::bail!("expected ternary");
    }
    Ok((&term.args[0], &term.args[1], &term.args[2]))
}

fn expect_quaternary(
    term: &raw::Term,
) -> anyhow::Result<(&raw::Node, &raw::Node, &raw::Node, &raw::Node)> {
    if term.args.len() != 4 {
        anyhow::bail!("expected quaternary");
    }
    Ok((&term.args[0], &term.args[1], &term.args[2], &term.args[3]))
}
