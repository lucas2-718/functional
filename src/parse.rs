



pub enum Token {
    NatInd(Box<AST>,Natural),
    EqInd(Box<AST>,Natural),
    Number(Natural),
    Nat,
    Equal(Box<AST>,Box<AST>),
    Refl(Box<AST>),
    Variable(Variable),
}

pub struct Variable(String);


pub enum AST {
    Token(Token),
    Lambda{
        arg: Variable,
        ty: Box<AST>,
        body: Box<AST>,
    },
    Application{
        func: Box<AST>,
        arg: Box<AST>,
    },
    Forall {
        arg: Variable,
        ty: Box<AST>,
        body: Box<AST>,
    }
}