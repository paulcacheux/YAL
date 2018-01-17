use ty::*;
use interner::{Interner, InternerId};
use codemap::Span;

pub mod prettyprinter;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IdentifierId(pub usize);

#[derive(Debug, Clone)]
pub struct Program {
    pub strings: Interner<String>,
    pub declarations: Vec<Function>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub return_ty: Type,
    pub name: String,
    pub parameters: Vec<(Type, IdentifierId)>,
    pub body: BlockStatement,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Block(BlockStatement),
    VarDecl {
        ty: Type,
        id: IdentifierId,
        init: Option<TypedExpression>,
    },
    If {
        condition: TypedExpression,
        body: BlockStatement,
        else_clause: BlockStatement,
    },
    While {
        condition: TypedExpression,
        body: BlockStatement,
    },
    Return(Option<TypedExpression>), // None for void
    Expression(TypedExpression),
    Break,
    Continue,
}

pub type BlockStatement = Vec<Statement>;

#[derive(Debug, Clone)]
pub struct TypedExpression {
    pub ty: Type,
    pub expr: Expression,
}

#[derive(Debug, Clone)]
pub enum Expression {
    Block(Box<BlockExpression>),
    LValueToRValue(Box<TypedExpression>),
    Literal(Literal),
    Identifier(IdentifierId),
    Assign {
        lhs: Box<TypedExpression>,
        rhs: Box<TypedExpression>,
    },
    BinaryOperator {
        binop: BinaryOperatorKind,
        lhs: Box<TypedExpression>,
        rhs: Box<TypedExpression>,
    },
    UnaryOperator {
        unop: UnaryOperatorKind,
        sub: Box<TypedExpression>,
    },
    Increment(Box<TypedExpression>),
    Decrement(Box<TypedExpression>),
    Subscript {
        array: Box<TypedExpression>,
        index: Box<TypedExpression>,
    },
    FunctionCall {
        function: String,
        args: Vec<TypedExpression>,
    },
    NewArray {
        sub_ty: Type,
        size: Box<TypedExpression>,
    },
    ArrayLength(Box<TypedExpression>),
}

#[derive(Debug, Clone)]
pub struct BlockExpression {
    pub stmts: BlockStatement,
    pub final_expr: TypedExpression,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Literal {
    IntLiteral(i64),
    DoubleLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(InternerId),
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOperatorKind {
    IntPlus,
    DoublePlus,
    IntMinus,
    DoubleMinus,
    IntMultiply,
    DoubleMultiply,
    IntDivide,
    DoubleDivide,
    IntModulo,
    IntEqual,
    DoubleEqual,
    BooleanEqual,
    IntNotEqual,
    DoubleNotEqual,
    BooleanNotEqual,
    IntLess,
    DoubleLess,
    IntLessEqual,
    DoubleLessEqual,
    IntGreater,
    DoubleGreater,
    IntGreaterEqual,
    DoubleGreaterEqual,
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOperatorKind {
    IntMinus,
    DoubleMinus,
    BooleanNot,
}