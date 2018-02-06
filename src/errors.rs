use std::fmt;
use std::convert::From;

use ty;
use ast;

#[derive(Debug, Clone)]
pub enum LexingError {
    UnparsableNumber,
    ReservedIdentifier(String),
    UnknownChar(char),
}

#[derive(Debug, Clone)]
pub enum ParsingError {
    LexingError(LexingError),
    Unexpected(Vec<String>),
    InvalidType,
    UnexpectedVoid,
}

#[derive(Debug, Clone)]
pub enum TranslationError {
    FunctionAlreadyDefined(String),
    ParameterAlreadyDefined(String),
    LocalAlreadyDefined(String),
    MismatchingTypes(ty::Type, ty::Type),
    UnexpectedType(ty::Type, ty::Type), // expected, given
    UndefinedLocal(String),
    UndefinedType(String),
    NonLValueAssign,
    BinOpUndefined(ast::BinaryOperatorKind, ty::Type, ty::Type),
    LazyOpUndefined(ast::LazyOperatorKind, ty::Type, ty::Type),
    UnOpUndefined(ast::UnaryOperatorKind, ty::Type),
    LValueUnOpUndefined(ast::LValueUnaryOperatorKind, ty::Type),
    CastUndefined(ty::Type, ty::Type),
    FunctionCallArityMismatch(usize, usize),
    FunctionUndefined(String),
    LValueUnopNonLValue,
    BreakContinueOutOfLoop,
    MainWrongType,
    NoMain,
    NotAllPathsReturn,
    SubscriptNotArray(ty::Type),
    LengthOnNonArray(ty::Type),
    MemberUndefined,
}

impl From<LexingError> for ParsingError {
    fn from(le: LexingError) -> ParsingError {
        ParsingError::LexingError(le)
    }
}

// hack needed for error propagation
use codemap::Spanned;
impl From<Spanned<LexingError>> for Spanned<ParsingError> {
    fn from(f: Spanned<LexingError>) -> Spanned<ParsingError> {
        Spanned {
            inner: ParsingError::from(f.inner),
            span: f.span,
        }
    }
}

impl fmt::Display for LexingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LexingError::UnparsableNumber => write!(f, "Can't parse this number"),
            LexingError::ReservedIdentifier(ref id) => {
                write!(f, "'{}' is a reserved identifier", id)
            }
            LexingError::UnknownChar(c) => write!(f, "Unknown char  '{}'", c),
        }
    }
}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ParsingError::LexingError(ref e) => e.fmt(f),
            ParsingError::Unexpected(ref expected) => write!(
                f,
                "Unexpected token, expected one of {}",
                expected.join(", ")
            ),
            ParsingError::InvalidType => write!(f, "Invalid type"),
            ParsingError::UnexpectedVoid => write!(
                f,
                "Unexpected void (can only be used as function return type or in pointers)"
            ),
        }
    }
}

impl fmt::Display for TranslationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TranslationError::FunctionAlreadyDefined(ref func) => {
                write!(f, "The function '{}' is already defined", func)
            }
            TranslationError::ParameterAlreadyDefined(ref param) => {
                write!(f, "The parameter '{}' is already defined", param)
            }
            TranslationError::LocalAlreadyDefined(ref local) => {
                write!(f, "The local '{}' is already defined", local)
            }
            TranslationError::MismatchingTypes(ref a, ref b) => {
                write!(f, "Mismatching types between '{:?}' and '{:?}'", a, b)
            }
            TranslationError::UnexpectedType(ref expected, ref given) => write!(
                f,
                "Unexpected type '{:?}' ('{:?}' expected).",
                given, expected
            ),
            TranslationError::UndefinedLocal(ref local) => {
                write!(f, "The local '{}' is undefined here", local)
            }
            TranslationError::UndefinedType(ref ty) => {
                write!(f, "The type '{}' is undefined here", ty)
            }
            TranslationError::NonLValueAssign => {
                write!(f, "Assignment to a value that can't be assigned")
            }
            TranslationError::BinOpUndefined(binop, ref a, ref b) => write!(
                f,
                "The binary operator '{:?}' can't be applied to '{:?}' and '{:?}'",
                binop, a, b
            ),
            TranslationError::LazyOpUndefined(lazyop, ref a, ref b) => write!(
                f,
                "The lazy operator '{:?}' can't be applied to '{:?}' and '{:?}'",
                lazyop, a, b
            ),
            TranslationError::UnOpUndefined(unop, ref a) => write!(
                f,
                "The unary operator '{:?}' can't be applied to '{:?}'",
                unop, a
            ),
            TranslationError::LValueUnOpUndefined(unop, ref a) => write!(
                f,
                "The lvalue unary operator '{:?}' can't be applied to '{:?}'",
                unop, a
            ),
            TranslationError::CastUndefined(ref a, ref b) => {
                write!(f, "Undefined cast between '{:?}' and '{:?}'", a, b)
            }
            TranslationError::FunctionCallArityMismatch(a, b) => write!(
                f,
                "Mismatching arities in function call between {} and {}",
                a, b
            ),
            TranslationError::FunctionUndefined(ref func) => {
                write!(f, "The function '{}' is undefined", func)
            }
            TranslationError::LValueUnopNonLValue => {
                write!(f, "LValue unary operator on a value that can't be assigned")
            }
            TranslationError::BreakContinueOutOfLoop => {
                write!(f, "Break or continue outside a loop")
            }
            TranslationError::MainWrongType => write!(f, "Main must be of type int()"),
            TranslationError::NoMain => write!(f, "A main function must be defined"),
            TranslationError::NotAllPathsReturn => {
                write!(f, "A path in this function doesn't return")
            }
            TranslationError::SubscriptNotArray(ref ty) => {
                write!(f, "Type '{:?}' can't be subscripted", ty)
            }
            TranslationError::LengthOnNonArray(ref ty) => {
                write!(f, "Type '{:?}' doesn't have a length property", ty)
            }
            TranslationError::MemberUndefined => write!(f, "Undefined member"),
        }
    }
}
