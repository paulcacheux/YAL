use ty::*;

mod symbol_table;
pub mod translator;

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

#[derive(Debug, Clone)]
pub enum Statement {
    Block(BlockStatement),
    VarDecl {
        ty: Type,
        name: VarName,
        value: Expression,
    },
    Assign {
        name: VarName,
        value: Expression,
    },
    Increment(VarName),
    Decrement(VarName),
    If {
        condition: VarName,
        body: BlockStatement,
        else_clause: BlockStatement,
    },
    Loop {
        body: BlockStatement,
    },
    Return(Option<VarName>),
    Break,
    Continue
}

#[derive(Debug, Clone)]
pub enum VarName {
    Id(String),
    Temp(usize)
}

pub type BlockStatement = Vec<Statement>;

#[derive(Debug, Clone)]
pub enum Expression {
    Literal(Literal),
    Var(VarName),
    BinaryOperator {
        binop: BinaryOperatorKind,
        lhs: VarName,
        rhs: VarName,
    },
    UnaryOperator {
        unop: UnaryOperatorKind,
        sub: VarName,
    },
    FunctionCall {
        function: String,
        args: Vec<VarName>
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    IntLiteral(i64),
    DoubleLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(String), // TODO intern
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
