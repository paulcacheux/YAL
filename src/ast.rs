use ty::*;

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
}

impl Function {
    pub fn get_type(&self) -> FunctionType {
        let return_ty = self.return_ty;
        let parameters_ty = self.parameters.iter().map(|&(a, _)| a).collect();
        FunctionType {
            return_ty,
            parameters_ty
        }
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Empty,
    Block(BlockStatement),
    VarDecl {
        ty: Type,
        declarations: Vec<(String, Option<Expression>)>
    },
    If {
        condition: Expression,
        body: Box<Statement>,
        else_clause: Option<Box<Statement>>,
    },
    While {
        condition: Expression,
        body: Box<Statement>,
    },
    Return(Option<Expression>),
    Expression(Expression),
    Break,
    Continue
}

pub type BlockStatement = Vec<Statement>;

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
        args: Vec<Expression>
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    IntLiteral(i64),
    DoubleLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(String),
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
