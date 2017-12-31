use std::fmt;

use parser::ParsingError;
use ir::translator::TranslationError;

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ParsingError::UnknownChar(c) => write!(f, "Unknown char  '{}'", c),
            ParsingError::Unexpected(ref expected) => {
                write!(f, "Unexpected token, expected one of {}", expected.join(", "))
            }
        }
    }
}

impl fmt::Display for TranslationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TranslationError::FunctionAlreadyDefined(ref func) => write!(f, "The function '{}' is already defined", func),
            TranslationError::ParameterAlreadyDefined(ref param) => write!(f, "The parameter '{}' is already defined", param),
            TranslationError::LocalAlreadyDefined(ref local) => write!(f, "The local '{}' is already defined", local),
            TranslationError::MismatchingTypes(ref a, ref b) => write!(f, "Mismatching types between '{:?}' and '{:?}'", a, b),
            TranslationError::UndefinedLocal(ref local) => write!(f, "The local '{}' is undefined here", local),
            TranslationError::NonLValueAssign => write!(f, "Assignment to a value that can't be assigned"),
            TranslationError::BinOpUndefined(binop, ref a, ref b) => write!(f, "The binary operator '{:?}' can't be applied to '{:?}' and '{:?}'", binop, a, b),
            TranslationError::LazyOpUndefined(lazyop, ref a, ref b) => write!(f, "The lazy operator '{:?}' can't be applied to '{:?}' and '{:?}'", lazyop, a, b),
            TranslationError::UnOpUndefined(unop, ref a) => write!(f, "The unary operator '{:?}' can't be applied to '{:?}'", unop, a),
            TranslationError::FunctionCallArity(a, b) => write!(f, "Mismatching arities in function call between {} and {}", a, b),
            TranslationError::FunctionUndefined(ref func) => write!(f, "The function '{}' is undefined", func),
            TranslationError::IncDecNonLValue => write!(f, "Increment or decrement to a value that can't be assigned"),
            TranslationError::BreakContinueOutOfLoop => write!(f, "Break or continue outside a loop"),
            TranslationError::MainWrongType => write!(f, "Main must be of type void(void)"),
            TranslationError::NoMain => write!(f, "A main function must be defined"),
            TranslationError::NotAllPathsReturn => write!(f, "A path in this function doesn't return"),
            TranslationError::SubscriptNotArray(ref ty) => write!(f, "Type '{:?}' can't be subscripted", ty),
        }
    }
}
