use codemap::Span;

#[derive(Debug, Clone, PartialEq)]
pub enum Token<'input> {
    EOF,
    // symbols
    LeftParenthesis,
    RightParenthesis,
    LeftBracket,
    RightBracket,
    LeftSquare,
    RightSquare,
    Dot,
    SemiColon,
    Comma,
    Colon,
    DotDotDot,
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
    ExternKeyword,
    StructKeyword,
    TypedefKeyword,
    WhileKeyword,
    ForKeyword,
    IfKeyword,
    ElseKeyword,
    ReturnKeyword,
    BreakKeyword,
    ContinueKeyword,
    NewKeyword,

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

#[derive(Debug, Clone, PartialEq)]
pub struct TokenAndSpan<'input> {
    pub token: Token<'input>,
    pub span: Span,
}

impl<'input> TokenAndSpan<'input> {
    pub fn new(token: Token<'input>, span: Span) -> Self {
        TokenAndSpan { token, span }
    }

    pub fn new_with_len(token: Token<'input>, start: usize, len: usize) -> Self {
        TokenAndSpan::new(token, Span::new_with_len(start, len))
    }
}
