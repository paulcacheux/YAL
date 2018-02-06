/// Represents a Token from a Javalette program.
///
/// Usually constructed by a `Lexer` and used by the `Parser` to build the `AST`.

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
    Amp,
    AmpAmp,
    Bang,
    Arrow,
    //keywords
    ExternKeyword,
    StructKeyword,
    WhileKeyword,
    ForKeyword,
    IfKeyword,
    ElseKeyword,
    ReturnKeyword,
    BreakKeyword,
    ContinueKeyword,
    AsKeyword,
    FnKeyword,
    LetKeyword,

    /*IntKeyword,
    DoubleKeyword,
    BooleanKeyword,
    VoidKeyword,
    StringKeyword,*/
    Identifier(&'input str),
    IntegerLiteral(i64),
    DoubleLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(&'input str),
}
