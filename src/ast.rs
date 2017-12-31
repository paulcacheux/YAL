use ty::*;
use string_interner::StringId;
use span::{Span, Spanned};

#[derive(Debug, Clone)]
pub struct Program {
    pub declarations: Vec<Declaration>,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Typedef(Typedef),
    Struct(Struct),
    Function(Function)
}

#[derive(Debug, Clone)]
pub struct Typedef {
    pub struct_name: String,
    pub ptr_name: String,
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub name: String,
    pub fields: Vec<(Type, String)>,
    pub span: Span,
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
    For(ForStatement),
    Return(Option<Spanned<Expression>>),
    Expression(Spanned<Expression>),
    Break,
    Continue,
}

#[derive(Debug, Clone)]
pub struct BlockStatement {
    pub statements: Vec<Spanned<Statement>>,
}

impl BlockStatement {
    pub fn from_vec(statements: Vec<Spanned<Statement>>) -> Self {
        BlockStatement {
            statements
        }
    }
}

#[derive(Debug, Clone)]
pub struct VarDeclarations {
    pub ty: Type,
    pub declarations: Vec<(String, Option<Spanned<Expression>>)>,
}

#[derive(Debug, Clone)]
pub struct IfStatement {
    pub condition: Spanned<Expression>,
    pub body: Box<Spanned<Statement>>,
    pub else_clause: Option<Box<Spanned<Statement>>>,
}

#[derive(Debug, Clone)]
pub struct WhileStatement {
    pub condition: Spanned<Expression>,
    pub body: Box<Spanned<Statement>>,
}

#[derive(Debug, Clone)]
pub struct ForStatement {
    pub ty: Type,
    pub name: String,
    pub array: Spanned<Expression>,
    pub body: Box<Spanned<Statement>>
}

#[derive(Debug, Clone)]
pub enum Expression {
    Literal(Literal),
    Identifier(String),
    Assign {
        lhs: Box<Spanned<Expression>>,
        rhs: Box<Spanned<Expression>>,
    },
    BinaryOperator {
        binop: BinaryOperatorKind,
        lhs: Box<Spanned<Expression>>,
        rhs: Box<Spanned<Expression>>,
    },
    LazyOperator {
        lazyop: LazyOperatorKind,
        lhs: Box<Spanned<Expression>>,
        rhs: Box<Spanned<Expression>>,
    },
    UnaryOperator {
        unop: UnaryOperatorKind,
        sub: Box<Spanned<Expression>>,
    },
    Increment(Box<Spanned<Expression>>),
    Decrement(Box<Spanned<Expression>>),
    Subscript {
        array: Box<Spanned<Expression>>,
        index: Box<Spanned<Expression>>,
    },
    FunctionCall {
        function: String,
        args: Vec<Spanned<Expression>>,
    },
    NewArray {
        ty: Type,
        sizes: Vec<Spanned<Expression>>,
    },
    MemberAccess {
        expr: Box<Spanned<Expression>>,
        member: String
    }
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
