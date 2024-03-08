#[derive(Debug)]
pub enum Node {
    Term(Term),
    Block(Block),
    Array(Array),
    Func(Func),
    Var(String),
    String(String),
}

#[derive(Debug)]
pub struct Block {
    pub nodes: Vec<Box<Node>>,
}

#[derive(Debug)]
pub struct Term {
    pub name: String,
    pub args: Vec<Box<Node>>,
}

#[derive(Debug)]
pub struct Array {
    pub elements: Vec<Box<Node>>,
}

#[derive(Debug)]
pub struct Func {
    pub name: String,
    pub id: usize,
}
