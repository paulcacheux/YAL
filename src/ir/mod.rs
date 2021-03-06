use ty::*;
use codemap::Span;
use common::Literal;

pub mod prettyprinter;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IdentifierId(pub usize);

#[derive(Debug, Clone)]
pub struct Program {
    pub declarations: Vec<Declaration>,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    ExternFunction(ExternFunction),
    Function(Function),
}

#[derive(Debug, Clone)]
pub struct ExternFunction {
    pub ty: FunctionType,
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub return_ty: Type,
    pub name: String,
    pub parameters: Vec<(Type, IdentifierId)>,
    pub var_declarations: Vec<VarDeclaration>,
    pub body: BlockStatement,
    pub span: Span,
}

impl Function {
    pub fn get_type(&self) -> FunctionType {
        let return_ty = self.return_ty;
        let parameters_ty = self.parameters.iter().map(|&(a, _)| a).collect();
        FunctionType {
            return_ty,
            parameters_ty,
            is_vararg: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct VarDeclaration {
    pub ty: Type,
    pub id: IdentifierId,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Block(BlockStatement),
    If {
        condition: Expression,
        body: BlockStatement,
        else_clause: BlockStatement,
    },
    For {
        init: Box<Statement>,
        condition: Expression,
        step: Option<Expression>,
        body: BlockStatement,
    },
    Return(Option<Expression>), // None for void
    Expression(Expression),
    Break,
    Continue,
}

pub type BlockStatement = Vec<Statement>;

#[derive(Debug, Clone)]
pub enum Expression {
    Block(Box<BlockExpression>),
    LValueToRValue(Box<Expression>),
    RValueToLValue(Box<Expression>),
    Value(Value),
    Assign {
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    BinaryOperator {
        binop: BinaryOperatorKind,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    UnaryOperator {
        unop: UnaryOperatorKind,
        sub: Box<Expression>,
    },
    LValueUnaryOperator {
        lvalue_unop: LValueUnaryOperatorKind,
        sub: Box<Expression>,
    },
    Cast {
        kind: CastKind,
        sub: Box<Expression>,
    },
    BitCast {
        dest_ty: Type,
        sub: Box<Expression>,
    },
    FunctionCall {
        function: Box<Expression>,
        args: Vec<Expression>,
    },
    FieldAccess {
        sub: Box<Expression>,
        index: usize,
    },
    Ternary {
        condition: Box<Expression>,
        true_expr: Box<Expression>,
        false_expr: Box<Expression>,
    },
}

#[derive(Debug, Clone)]
pub struct BlockExpression {
    pub stmts: BlockStatement,
    pub final_expr: Expression,
}

#[derive(Debug, Clone)]
pub enum Value {
    Literal(Literal),
    Local(IdentifierId),
    Global(String),
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

    PtrPlusOffset,
    PtrMinusOffset,
    PtrDiff,
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOperatorKind {
    IntMinus,
    DoubleMinus,
    BooleanNot,
    PointerDeref,
}

#[derive(Debug, Clone, Copy)]
pub enum LValueUnaryOperatorKind {
    IntIncrement,
    IntDecrement,
    LValueToPtr,
}

#[derive(Debug, Clone, Copy)]
pub enum CastKind {
    IntToDouble,
    DoubleToInt,
    BooleanToInt,
    IntToBoolean,
    PtrToInt,
    IntToPtr(Type),
}
