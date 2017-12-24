use regex::Regex;
use parser::ParsingError;

mod token;
pub use self::token::Token;

lazy_static! {
    static ref WHITESPACES: Regex = Regex::new(r"^\s+").unwrap();
    static ref LINE_COMMENT: Regex = Regex::new(r"^//.*").unwrap();
    static ref LINE_PP_COMMENT: Regex = Regex::new(r"^#.*").unwrap();
    static ref BLOCK_COMMENT: Regex = Regex::new(r"^/\*(.|[\r\n])*?\*/").unwrap();
    static ref SKIPABLE: Vec<&'static Regex> = vec![
        &WHITESPACES, &LINE_COMMENT, &LINE_PP_COMMENT, &BLOCK_COMMENT
    ];

    static ref IDENTIFIER_REGEX: Regex = Regex::new(r"^[a-zA-Z_][a-zA-Z0-9_]*").unwrap();
    static ref INTEGER_REGEX: Regex = Regex::new(r"^[0-9]+").unwrap();
    static ref DOUBLE_REGEX: Regex = Regex::new(r"^[0-9]*\.[0-9]+([eE][+-]?[0-9]+)?").unwrap();
    static ref STRING_REGEX: Regex = Regex::new(r##"^"(([^"]|\\")*[^\\])?""##).unwrap();
}

pub struct Lexer<'input> {
    input: &'input str,
    pos: usize,
    buffer: Option<Token<'input>>
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer {
            input,
            pos: 0,
            buffer: None
        }
    }

    pub fn skip_whitespaces(&mut self) {
        'main_loop: loop {
            for regex in SKIPABLE.iter() {
                if let Some(m) = regex.find(&self.input[self.pos..]) {
                    self.pos += m.end();
                    continue 'main_loop
                } 
            }
            break
        }
    }

    fn match_regex(&mut self, regex: &Regex) -> Option<&'input str> {
        regex.find(&self.input[self.pos..]).map(|m| {
            let new_pos = self.pos + m.end();
            let token_str = &self.input[self.pos..new_pos];
            self.pos = new_pos;
            token_str
        })
    }

    pub fn peek_token(&mut self) -> Result<&Token<'input>, ParsingError> {
        if self.buffer.is_none() {
            self.buffer = Some(self.next_token()?);
        }

        if let Some(ref tok) = self.buffer {
            Ok(tok)
        } else {
            unreachable!()
        }
    }

    pub fn next_token(&mut self) -> Result<Token<'input>, ParsingError> {
        macro_rules! match_literal {
            ($lexer:expr; $literal:tt => $ret_expr:expr) => {
                if (&$lexer.input[$lexer.pos..]).starts_with($literal) {
                    $lexer.pos += $literal.len();
                    return Ok($ret_expr)
                }
            }
        }

        if let Some(token) = self.buffer.take() {
            return Ok(token)
        }

        self.skip_whitespaces();

        if self.pos >= self.input.len() {
            return Ok(Token::EOF)
        }

        match_literal!(self; "(" => Token::LeftParenthesis);
        match_literal!(self; ")" => Token::RightParenthesis);
        match_literal!(self; "{" => Token::LeftBracket);
        match_literal!(self; "}" => Token::RightBracket);
        match_literal!(self; ";" => Token::SemiColon);
        match_literal!(self; "," => Token::Comma);

        match_literal!(self; "==" => Token::EqualEqual);
        match_literal!(self; "!=" => Token::BangEqual);
        match_literal!(self; "++" => Token::PlusPlus);
        match_literal!(self; "--" => Token::MinusMinus);
        match_literal!(self; "<=" => Token::LessEqual);
        match_literal!(self; ">=" => Token::GreaterEqual);
        match_literal!(self; "||" => Token::PipePipe);
        match_literal!(self; "&&" => Token::AmpAmp);

        match_literal!(self; "=" => Token::Equal);
        match_literal!(self; "+" => Token::Plus);
        match_literal!(self; "-" => Token::Minus);
        match_literal!(self; "*" => Token::Star);
        match_literal!(self; "/" => Token::Slash);
        match_literal!(self; "%" => Token::Percent);
        match_literal!(self; "<" => Token::Less);
        match_literal!(self; ">" => Token::Greater);
        match_literal!(self; "!" => Token::Bang);

        if let Some(s) = self.match_regex(&IDENTIFIER_REGEX) {
            return match s {
                "while" => Ok(Token::WhileKeyword),
                "if" => Ok(Token::IfKeyword),
                "else" => Ok(Token::ElseKeyword),
                "return" => Ok(Token::ReturnKeyword),
                "true" => Ok(Token::BooleanLiteral(true)),
                "false" => Ok(Token::BooleanLiteral(false)),
                "int" => Ok(Token::IntKeyword),
                "double" => Ok(Token::DoubleKeyword),
                "boolean" => Ok(Token::BooleanKeyword),
                "void" => Ok(Token::VoidKeyword),
                "continue" => Ok(Token::ContinueKeyword),
                "break" => Ok(Token::BreakKeyword),
                s => Ok(Token::Identifier(s))
            }
        }
        if let Some(s) = self.match_regex(&DOUBLE_REGEX) {
            return Ok(Token::DoubleLiteral(s.parse().unwrap()))
        }
        if let Some(s) = self.match_regex(&INTEGER_REGEX) {
            return Ok(Token::IntegerLiteral(s.parse().unwrap()))
        }
        if let Some(s) = self.match_regex(&STRING_REGEX) {
            return Ok(Token::StringLiteral(s))
        }

        return Err(ParsingError::UnknownChar(
                (&self.input[self.pos..]).chars().next().unwrap())
        )
    }
}
