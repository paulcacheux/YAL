use lexer::{Token, Lexer};
use ast;
use ty;

mod parsing_error;
mod expression_parser;

pub use self::parsing_error::ParsingError;
use self::expression_parser::*;

pub struct Parser<'input> {
    pub lexer: Lexer<'input>
}

macro_rules! accept {
    ($lexer:expr; $expect:pat => $ret:expr, $($expected:expr),*) => {
        if let $expect = $lexer.next_token()? {
           $ret
        } else {
            return_unexpected!($($expected),*);
        }
    }
}

macro_rules! expect {
    ($lexer:expr; $expect:pat, $($expected:expr),*) => {
        accept!($lexer; $expect => {}, $($expected),*)
    }
}

macro_rules! return_unexpected {
    ($($expected:expr),*) => {
        return Err(ParsingError::Unexpected(vec![$($expected.into()),*]));
    }
}

pub type ParsingResult<T> = Result<T, ParsingError>;

impl<'input> Parser<'input> {
    pub fn new(lexer: Lexer<'input>) -> Parser {
        Parser {
            lexer
        }
    }

    pub fn parse_program(&mut self) -> ParsingResult<ast::Program> {
        let mut declarations = Vec::new();

        loop {
            if let Token::EOF = *self.lexer.peek_token()? {
                break
            }

            declarations.push(self.parse_function_declaration()?);
        }
        Ok(ast::Program {
            declarations
        })
    }

    pub fn parse_type(&mut self) -> ParsingResult<ty::Type> {
        match self.lexer.next_token()? {
            Token::IntKeyword => Ok(ty::Type::Int),
            Token::DoubleKeyword => Ok(ty::Type::Double),
            Token::BooleanKeyword => Ok(ty::Type::Boolean),
            Token::VoidKeyword => Ok(ty::Type::Void),
            _ => return_unexpected!("int", "boolean", "double", "void")
        }
    }

    pub fn parse_type_non_void(&mut self) -> ParsingResult<ty::Type> {
        match self.lexer.next_token()? {
            Token::IntKeyword => Ok(ty::Type::Int),
            Token::DoubleKeyword => Ok(ty::Type::Double),
            Token::BooleanKeyword => Ok(ty::Type::Boolean),
            _ => return_unexpected!("int", "boolean", "double")
        }
    }

    pub fn parse_function_declaration(&mut self) -> ParsingResult<ast::Function> {
        let return_ty = self.parse_type()?;
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let parameters = self.parse_parameter_list()?;
        expect!(self.lexer; Token::RightParenthesis, ")");
        let body = self.parse_block_statement()?;

        Ok(ast::Function {
            return_ty,
            name,
            parameters,
            body
        })
    }

    pub fn parse_parameter_list(&mut self) -> ParsingResult<Vec<(ty::Type, String)>> {
        let mut result = Vec::new();

        if let Token::RightParenthesis = *self.lexer.peek_token()? {
            return Ok(result)
        }

        result.push(self.parse_parameter()?);
        while let Token::Comma = *self.lexer.peek_token()? {
            self.lexer.next_token()?;

            result.push(self.parse_parameter()?);
        }

        Ok(result)
    }

    pub fn parse_parameter(&mut self) -> ParsingResult<(ty::Type, String)> {
        let ty = self.parse_type_non_void()?;
        let name = self.parse_identifier()?;
        Ok((ty, name))
    }

    pub fn parse_identifier(&mut self) -> ParsingResult<String> {
        Ok(accept!(self.lexer; Token::Identifier(id) => id.to_string(), "identifier"))
    }

    pub fn parse_block_statement(&mut self) -> ParsingResult<ast::BlockStatement> {
        let mut block = Vec::new();
        expect!(self.lexer; Token::LeftBracket, "{");
        loop {
            if let Token::RightBracket = *self.lexer.peek_token()? {
                break
            }

            block.push(self.parse_statement()?);
        }
        expect!(self.lexer; Token::RightBracket, "}");

        Ok(block)
    }

    pub fn parse_statement(&mut self) -> ParsingResult<ast::Statement> {
        match *self.lexer.peek_token()? {
            Token::SemiColon => {
                self.lexer.next_token()?;
                Ok(ast::Statement::Empty)
            },
            Token::IfKeyword => self.parse_if_statement(),
            Token::WhileKeyword => self.parse_while_statement(),
            Token::ReturnKeyword => self.parse_return_statement(),
            Token::LeftBracket => {
                Ok(ast::Statement::Block(self.parse_block_statement()?))
            },
            Token::BreakKeyword => Ok(ast::Statement::Break),
            Token::ContinueKeyword => Ok(ast::Statement::Continue),
            Token::IntKeyword |
            Token::DoubleKeyword |
            Token::BooleanKeyword => self.parse_var_declaration(),
            _ => {
                let expr = ast::Statement::Expression(self.parse_expression()?);
                expect!(self.lexer; Token::SemiColon, ";");
                Ok(expr)
            }
        }
    }

    pub fn parse_if_statement(&mut self) -> ParsingResult<ast::Statement> {
        expect!(self.lexer; Token::IfKeyword, "if");
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let condition = self.parse_expression()?;
        expect!(self.lexer; Token::RightParenthesis, ")");
        let body = Box::new(self.parse_statement()?);

        let else_clause = if let Token::ElseKeyword = *self.lexer.peek_token()? {
            self.lexer.next_token()?;
            let body = Box::new(self.parse_statement()?);
            Some(body)
        } else {
            None
        };

        Ok(ast::Statement::If {
            condition,
            body,
            else_clause
        })
    }

    pub fn parse_while_statement(&mut self) -> ParsingResult<ast::Statement> {
        expect!(self.lexer; Token::WhileKeyword, "if");
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let condition = self.parse_expression()?;
        expect!(self.lexer; Token::RightParenthesis, ")");
        let body = Box::new(self.parse_statement()?);

        Ok(ast::Statement::While {
            condition,
            body,
        })
    }

    pub fn parse_return_statement(&mut self) -> ParsingResult<ast::Statement> {
        expect!(self.lexer; Token::ReturnKeyword, "return");
        let expr = if let Token::SemiColon = *self.lexer.peek_token()? {
            None
        } else {
            Some(self.parse_expression()?)
        };
        expect!(self.lexer; Token::SemiColon, ";");
        Ok(ast::Statement::Return(expr))
    }

    pub fn parse_identifier_and_maybe_value(&mut self) -> ParsingResult<(String, Option<ast::Expression>)> {
        let name = self.parse_identifier()?;
        let expr = if let Token::Equal = *self.lexer.peek_token()? {
            self.lexer.next_token()?;
            Some(self.parse_expression()?)
        } else {
            None
        };
        Ok((name, expr))
    }

    pub fn parse_var_declaration(&mut self) -> ParsingResult<ast::Statement> {
        let ty = self.parse_type_non_void()?;
        let mut declarations = Vec::new();

        declarations.push(self.parse_identifier_and_maybe_value()?);
        while let Token::Comma = *self.lexer.peek_token()? {
            self.lexer.next_token()?;
            declarations.push(self.parse_identifier_and_maybe_value()?);
        }
        expect!(self.lexer; Token::SemiColon, ";");
        Ok(ast::Statement::VarDecl {
            ty,
            declarations
        })
    }

    pub fn parse_expression(&mut self) -> ParsingResult<ast::Expression> {
        let lhs = self.parse_incdec_expression()?;
        parse_expression_inner(self, lhs, 0)
    }

    pub fn parse_incdec_expression(&mut self) -> ParsingResult<ast::Expression> {
        let mut sub = self.parse_leaf_expression()?;
        loop {
            match *self.lexer.peek_token()? {
                Token::PlusPlus => {
                    self.lexer.next_token()?;
                    sub = ast::Expression::Increment(Box::new(sub));
                    continue
                },
                Token::MinusMinus => {
                    self.lexer.next_token()?;
                    sub = ast::Expression::Decrement(Box::new(sub));
                    continue
                },
                _ => break
            }
        }
        Ok(sub)
    }

    pub fn parse_leaf_expression(&mut self) -> ParsingResult<ast::Expression> {
        match self.lexer.next_token()? {
            Token::IntegerLiteral(i)
                => Ok(ast::Expression::Literal(ast::Literal::IntLiteral(i))),
            Token::DoubleLiteral(d)
                => Ok(ast::Expression::Literal(ast::Literal::DoubleLiteral(d))),
            Token::BooleanLiteral(b)
                => Ok(ast::Expression::Literal(ast::Literal::BooleanLiteral(b))),
            Token::StringLiteral(s) // TODO parse string (escape, etc)
                => Ok(ast::Expression::Literal(ast::Literal::StringLiteral(s.to_string()))),
            Token::Minus => {
                let sub = self.parse_incdec_expression()?;
                Ok(ast::Expression::UnaryOperator {
                    unop: ast::UnaryOperatorKind::Minus,
                    sub: Box::new(sub)
                })
            },
            Token::Bang => {
                let sub = self.parse_incdec_expression()?;
                Ok(ast::Expression::UnaryOperator {
                    unop: ast::UnaryOperatorKind::LogicalNot,
                    sub: Box::new(sub)
                })
            },
            Token::LeftParenthesis => {
                let expr = self.parse_expression()?;
                expect!(self.lexer; Token::RightParenthesis, ")");
                Ok(expr)
            },
            Token::Identifier(id) => {
                let name = id.to_string();
                if let Token::LeftParenthesis = *self.lexer.peek_token()? {
                    self.lexer.next_token()?;
                    let args = self.parse_expression_list()?;
                    expect!(self.lexer; Token::RightParenthesis, ")");
                    Ok(ast::Expression::FunctionCall {
                        function: name,
                        args
                    })
                } else {
                    Ok(ast::Expression::Identifier(name))
                }
            },
            _ => {
                return_unexpected!("literal", "(", "-", "!", "identifier");
            }
        }
    }

    pub fn parse_expression_list(&mut self) -> ParsingResult<Vec<ast::Expression>> {
        let mut result = Vec::new();

        if let Token::RightParenthesis = *self.lexer.peek_token()? {
            return Ok(result)
        }

        result.push(self.parse_expression()?);
        while let Token::Comma = *self.lexer.peek_token()? {
            self.lexer.next_token()?;

            result.push(self.parse_expression()?);
        }

        Ok(result)
    }
}
