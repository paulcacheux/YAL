use std::fmt;
use std::convert::From;

use ty;
use ast;

#[derive(Debug, Clone)]
pub enum UserError {
    Parsing(ParsingError),
    Translation(TranslationError),
}

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
    TypeAlreadyDefined(String),
    FieldAlreadyDefined(String),
    MismatchingTypes(ty::Type, ty::Type),
    UnexpectedType(ty::Type, ty::Type), // expected, given
    NonStructType(String),
    StructCycle(String),
    UndefinedLocal(String),
    UndefinedType(String),
    NonLValueAssign,
    FieldAreadySet(String),
    FieldNotSet,
    UndefinedField(String),
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
    UnexpectedVoid,
}

impl From<ParsingError> for UserError {
    fn from(pe: ParsingError) -> UserError {
        UserError::Parsing(pe)
    }
}

impl From<TranslationError> for UserError {
    fn from(te: TranslationError) -> UserError {
        UserError::Translation(te)
    }
}

impl From<LexingError> for ParsingError {
    fn from(le: LexingError) -> ParsingError {
        ParsingError::LexingError(le)
    }
}

use codemap::Spanned;
macro_rules! spanned_hack {
    ($from:ty => $to:ty) => {
        impl From<Spanned<$from>> for Spanned<$to> {
            fn from(f: Spanned<$from>) -> Spanned<$to> {
                Spanned {
                    inner: f.inner.into(),
                    span: f.span,
                }
            }
        }
    }
}

spanned_hack!(LexingError => ParsingError);
spanned_hack!(ParsingError => UserError);
spanned_hack!(TranslationError => UserError);

impl fmt::Display for UserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            UserError::Parsing(ref pe) => <ParsingError as fmt::Display>::fmt(pe, f),
            UserError::Translation(ref te) => <TranslationError as fmt::Display>::fmt(te, f),
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
            TranslationError::TypeAlreadyDefined(ref ty) => {
                write!(f, "The type '{}' is already defined", ty)
            }
            TranslationError::FieldAlreadyDefined(ref field) => {
                write!(f, "The field '{}' is already defined", field)
            }
            TranslationError::MismatchingTypes(ref a, ref b) => {
                write!(f, "Mismatching types between '{}' and '{}'", a, b)
            }
            TranslationError::UnexpectedType(ref expected, ref given) => {
                write!(f, "Unexpected type '{}' ('{}' expected).", given, expected)
            }
            TranslationError::NonStructType(ref name) => {
                write!(f, "'{}' is not a struct type", name)
            }
            TranslationError::StructCycle(ref name) => write!(
                f,
                "The struct '{}' is cyclic (of infinite size), maybe use a pointer",
                name
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
            TranslationError::FieldAreadySet(ref field) => write!(
                f,
                "The field '{}' has already been set in this literal",
                field
            ),
            TranslationError::FieldNotSet => {
                write!(f, "Not all fields are set in this struct literal")
            }
            TranslationError::UndefinedField(ref field) => {
                write!(f, "The field '{}' doesn't exist here", field)
            }
            TranslationError::BinOpUndefined(binop, ref a, ref b) => write!(
                f,
                "The binary operator '{:?}' can't be applied to '{}' and '{}'",
                binop, a, b
            ),
            TranslationError::LazyOpUndefined(lazyop, ref a, ref b) => write!(
                f,
                "The lazy operator '{:?}' can't be applied to '{}' and '{}'",
                lazyop, a, b
            ),
            TranslationError::UnOpUndefined(unop, ref a) => write!(
                f,
                "The unary operator '{:?}' can't be applied to '{}'",
                unop, a
            ),
            TranslationError::LValueUnOpUndefined(unop, ref a) => write!(
                f,
                "The lvalue unary operator '{:?}' can't be applied to '{}'",
                unop, a
            ),
            TranslationError::CastUndefined(ref a, ref b) => {
                write!(f, "Undefined cast between '{}' and '{}'", a, b)
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
                write!(f, "Type '{}' can't be subscripted", ty)
            }
            TranslationError::LengthOnNonArray(ref ty) => {
                write!(f, "Type '{}' doesn't have a length property", ty)
            }
            TranslationError::MemberUndefined => write!(f, "Undefined member"),
            TranslationError::UnexpectedVoid => write!(f, "Void type can't be used here"),
        }
    }
}
