use span::Spanned;

#[derive(Debug, Clone)]
pub enum ParsingError {
    ReservedIdentifier(String),
    UnknownChar(char),
    Unexpected(Vec<String>),
}

pub type ParsingResult<T> = Result<T, Spanned<ParsingError>>;
