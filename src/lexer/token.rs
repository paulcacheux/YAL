#[derive(Debug, Clone, PartialEq)]
pub enum Token<'input> {
    EOF,
    // symbols
    LeftParenthesis,
    RightParenthesis,
    LeftBracket,
    RightBracket,
    SemiColon,
    Comma,
    // operators
    Equal,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    PlusPlus,
    MinusMinus,
    EqualEqual,
    BangEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    PipePipe,
    AmpAmp,
    Bang,
    //keywords
    WhileKeyword,
    IfKeyword,
    ElseKeyword,
    ReturnKeyword,
    BreakKeyword,
    ContinueKeyword,

    IntKeyword,
    DoubleKeyword,
    BooleanKeyword,
    VoidKeyword,


    Identifier(&'input str),
    IntegerLiteral(i64),
    DoubleLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(&'input str),
}
