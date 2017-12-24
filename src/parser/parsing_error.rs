#[derive(Debug, Clone)]
pub enum ParsingError {
    UnknownChar(char),
    Unexpected(Vec<String>),
}
