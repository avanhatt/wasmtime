#[derive(Debug)]
pub enum Node {
    Term { name: String, args: Vec<Box<Node>> },
    Block(Block),
    Array { nodes: Vec<Box<Node>> },
    Func { name: String, id: usize },
    Var { name: String },
    String { value: String },
}

#[derive(Debug)]
pub struct Block {
    pub nodes: Vec<Box<Node>>,
}
