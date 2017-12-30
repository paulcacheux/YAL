use ty::*;
use string_interner::StringId;
use span::{Span, Spanned};

#[derive(Debug, Clone)]
pub struct Program {
    pub declarations: Vec<Function>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub return_ty: Type,
    pub name: String,
    pub parameters: Vec<(Type, String)>,
    pub body: BlockStatement,
    pub span: Span,
}

impl Function {
    pub fn get_type(&self) -> FunctionType {
        let return_ty = self.return_ty.clone();
        let parameters_ty = self.parameters
            .iter()
            .map(|&(ref a, _)| a.clone())
            .collect();
        FunctionType {
            return_ty,
            parameters_ty,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Empty,
    Block(BlockStatement),
    VarDecl(VarDeclarations),
    If(IfStatement),
    While(WhileStatement),
    Return(Option<Expression>),
    Expression(Expression),
    Break,
    Continue,
}

#[derive(Debug, Clone)]
pub struct BlockStatement {
    pub statements: Vec<Spanned<Statement>>,
}

impl BlockStatement {
    pub fn new() -> Self {
        BlockStatement::from_vec(vec![])
    }

    pub fn from_vec(statements: Vec<Spanned<Statement>>) -> Self {
        BlockStatement {
            statements
        }
    }
}

#[derive(Debug, Clone)]
pub struct VarDeclarations {
    pub ty: Type,
    pub declarations: Vec<(String, Option<Expression>)>,
}

#[derive(Debug, Clone)]
pub struct IfStatement {
    pub condition: Expression,
    pub body: Box<Spanned<Statement>>,
    pub else_clause: Option<Box<Spanned<Statement>>>,
}

#[derive(Debug, Clone)]
pub struct WhileStatement {
    pub condition: Expression,
    pub body: Box<Spanned<Statement>>,
}

#[derive(Debug, Clone)]
pub enum Expression {
    Literal(Literal),
    Identifier(String),
    Assign {
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    BinaryOperator {
        binop: BinaryOperatorKind,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    LazyOperator {
        lazyop: LazyOperatorKind,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    UnaryOperator {
        unop: UnaryOperatorKind,
        sub: Box<Expression>,
    },
    Increment(Box<Expression>),
    Decrement(Box<Expression>),
    FunctionCall {
        function: String,
        args: Vec<Expression>,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum Literal {
    IntLiteral(i64),
    DoubleLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(StringId),
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOperatorKind {
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

#[derive(Debug, Clone, Copy)]
pub enum LazyOperatorKind {
    LogicalAnd,
    LogicalOr,
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOperatorKind {
    Minus,
    LogicalNot,
}
