use lexer::{Lexer, Token, TokenAndSpan};
use ast;
use ty;
use string_interner::StringInterner;
use span::{Span, Spanned};

mod parsing_error;
mod expression_parser;

pub use self::parsing_error::ParsingError;
use self::expression_parser::*;

pub struct Parser<'si, 'input> {
    pub lexer: Lexer<'input>,
    pub string_interner: &'si mut StringInterner,
}

macro_rules! accept {
    ($lexer:expr; $expect:pat => $ret:expr, $($expected:expr),*) => {
        {
            let TokenAndSpan { token, span } = $lexer.next_token()?;
            if let $expect = token {
                ($ret, span)
            } else {
                return_unexpected!($($expected),*);
            }
        }
    }
}

macro_rules! expect {
    ($lexer:expr; $expect:pat, $($expected:expr),*) => {
        accept!($lexer; $expect => {}, $($expected),*).1
    }
}

macro_rules! return_unexpected {
    ($($expected:expr),*) => {
        return Err(ParsingError::Unexpected(vec![$($expected.into()),*]));
    }
}

pub type ParsingResult<T> = Result<T, ParsingError>;

impl<'si, 'input> Parser<'si, 'input> {
    pub fn new(lexer: Lexer<'input>, string_interner: &'si mut StringInterner) -> Self {
        Parser {
            lexer,
            string_interner,
        }
    }

    pub fn parse_program(&mut self) -> ParsingResult<ast::Program> {
        let mut declarations = Vec::new();

        loop {
            if let Token::EOF = self.lexer.peek_token()?.token {
                break;
            }

            declarations.push(self.parse_function_declaration()?);
        }
        Ok(ast::Program { declarations })
    }

    pub fn parse_type(&mut self) -> ParsingResult<Spanned<ty::Type>> {
        let TokenAndSpan { token, span } = self.lexer.next_token()?;
        let ty = match token {
            Token::IntKeyword => ty::Type::Int,
            Token::DoubleKeyword => ty::Type::Double,
            Token::BooleanKeyword => ty::Type::Boolean,
            Token::VoidKeyword => ty::Type::Void,
            _ => return_unexpected!("int", "boolean", "double", "void"),
        };
        Ok(Spanned::new(ty, span))
    }

    pub fn parse_type_non_void(&mut self) -> ParsingResult<Spanned<ty::Type>> {
        let TokenAndSpan { token, span } = self.lexer.next_token()?;
        let ty = match token {
            Token::IntKeyword => ty::Type::Int,
            Token::DoubleKeyword => ty::Type::Double,
            Token::BooleanKeyword => ty::Type::Boolean,
            _ => return_unexpected!("int", "boolean", "double"),
        };
        Ok(Spanned::new(ty, span))
    }

    pub fn parse_function_declaration(&mut self) -> ParsingResult<ast::Function> {
        let Spanned { inner: return_ty, span: ty_span } = self.parse_type()?;
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let parameters = self.parse_parameter_list()?;
        expect!(self.lexer; Token::RightParenthesis, ")");
        let Spanned { inner: body, span: body_span } = self.parse_block_statement()?;

        let span = Span::merge(ty_span, body_span);

        Ok(ast::Function {
            return_ty,
            name,
            parameters,
            body,
            span
        })
    }

    pub fn parse_parameter_list(&mut self) -> ParsingResult<Vec<(ty::Type, String)>> {
        let mut result = Vec::new();

        if let Token::RightParenthesis = self.lexer.peek_token()?.token {
            return Ok(result);
        }

        result.push(self.parse_parameter()?);
        while let Token::Comma = self.lexer.peek_token()?.token {
            self.lexer.next_token()?;

            result.push(self.parse_parameter()?);
        }

        Ok(result)
    }

    pub fn parse_parameter(&mut self) -> ParsingResult<(ty::Type, String)> {
        let ty = self.parse_type_non_void()?.inner;
        let name = self.parse_identifier()?;
        Ok((ty, name))
    }

    pub fn parse_identifier(&mut self) -> ParsingResult<String> {
        let (id, _) = accept!(self.lexer; Token::Identifier(id) => id.to_string(), "identifier");
        Ok(id)
    }

    pub fn parse_block_statement(&mut self) -> ParsingResult<Spanned<ast::BlockStatement>> {
        let mut block = Vec::new();
        let begin_span = expect!(self.lexer; Token::LeftBracket, "{");
        loop {
            if let Token::RightBracket = self.lexer.peek_token()?.token {
                break;
            }

            block.push(self.parse_statement()?);
        }
        let end_span = expect!(self.lexer; Token::RightBracket, "}");
        let span = Span::merge(begin_span, end_span);

        Ok(Spanned::new(ast::BlockStatement::from_vec(block), span))
    }

    pub fn parse_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let span = self.lexer.peek_token()?.span;
        match self.lexer.peek_token()?.token {
            Token::SemiColon => {
                let span = self.lexer.next_token()?.span;
                Ok(Spanned::new(ast::Statement::Empty, span))
            },
            Token::IfKeyword => self.parse_if_statement(),
            Token::WhileKeyword => self.parse_while_statement(),
            Token::ReturnKeyword => self.parse_return_statement(),
            Token::LeftBracket => {
                let Spanned { inner: block, span } = self.parse_block_statement()?;
                let stmt = Spanned::new(ast::Statement::Block(block), span);
                Ok(stmt)
            },
            Token::BreakKeyword => {
                let span = self.lexer.next_token()?.span;
                Ok(Spanned::new(ast::Statement::Break, span))
            },
            Token::ContinueKeyword => {
                let span = self.lexer.next_token()?.span;
                Ok(Spanned::new(ast::Statement::Continue, span))
            },
            Token::IntKeyword | Token::DoubleKeyword | Token::BooleanKeyword => {
                self.parse_var_declaration()
            }
            _ => {
                let expr = ast::Statement::Expression(self.parse_expression()?);
                let end_span = expect!(self.lexer; Token::SemiColon, ";");
                let span = Span::merge(span, end_span);
                Ok(Spanned::new(expr, span))
            }
        }
    }

    pub fn parse_if_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let begin_span = expect!(self.lexer; Token::IfKeyword, "if");
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let condition = self.parse_expression()?;
        expect!(self.lexer; Token::RightParenthesis, ")");
        let body = Box::new(self.parse_statement()?);

        let else_clause = if let Token::ElseKeyword = self.lexer.peek_token()?.token {
            self.lexer.next_token()?;
            let body = Box::new(self.parse_statement()?);
            Some(body)
        } else {
            None
        };

        let end_span = if let &Some(ref e) = &else_clause {
            e.span
        } else {
            body.span
        };
        let span = Span::merge(begin_span, end_span);

        Ok(Spanned::new(ast::Statement::If(ast::IfStatement {
            condition,
            body,
            else_clause,
        }), span))
    }

    pub fn parse_while_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let begin_span = expect!(self.lexer; Token::WhileKeyword, "while");
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let condition = self.parse_expression()?;
        expect!(self.lexer; Token::RightParenthesis, ")");
        let body = Box::new(self.parse_statement()?);

        let span = Span::merge(begin_span, body.span);

        Ok(Spanned::new(ast::Statement::While(ast::WhileStatement {
            condition,
            body,
        }), span))
    }

    pub fn parse_return_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let begin_span = expect!(self.lexer; Token::ReturnKeyword, "return");
        let expr = if let Token::SemiColon = self.lexer.peek_token()?.token {
            None
        } else {
            Some(self.parse_expression()?)
        };
        let end_span = expect!(self.lexer; Token::SemiColon, ";");

        let span = Span::merge(begin_span, end_span);

        Ok(Spanned::new(ast::Statement::Return(expr), span))
    }

    pub fn parse_identifier_and_maybe_value(
        &mut self,
    ) -> ParsingResult<(String, Option<ast::Expression>)> {
        let name = self.parse_identifier()?;
        let expr = if let Token::Equal = self.lexer.peek_token()?.token {
            self.lexer.next_token()?;
            Some(self.parse_expression()?)
        } else {
            None
        };
        Ok((name, expr))
    }

    pub fn parse_var_declaration(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let Spanned { inner: ty, span: ty_span } = self.parse_type_non_void()?;
        let mut declarations = Vec::new();

        declarations.push(self.parse_identifier_and_maybe_value()?);
        while let Token::Comma = self.lexer.peek_token()?.token {
            self.lexer.next_token()?;
            declarations.push(self.parse_identifier_and_maybe_value()?);
        }
        let end_span = expect!(self.lexer; Token::SemiColon, ";");

        let span = Span::merge(ty_span, end_span);

        Ok(Spanned::new(ast::Statement::VarDecl(ast::VarDeclarations {
            ty,
            declarations,
        }), span))
    }

    pub fn parse_expression(&mut self) -> ParsingResult<ast::Expression> {
        let lhs = self.parse_incdec_expression()?;
        parse_expression_inner(self, lhs, 0)
    }

    pub fn parse_incdec_expression(&mut self) -> ParsingResult<ast::Expression> {
        let mut sub = self.parse_leaf_expression()?;
        loop {
            match self.lexer.peek_token()?.token {
                Token::PlusPlus => {
                    self.lexer.next_token()?;
                    sub = ast::Expression::Increment(Box::new(sub));
                    continue;
                }
                Token::MinusMinus => {
                    self.lexer.next_token()?;
                    sub = ast::Expression::Decrement(Box::new(sub));
                    continue;
                }
                _ => break,
            }
        }
        Ok(sub)
    }

    pub fn parse_leaf_expression(&mut self) -> ParsingResult<ast::Expression> {
        let TokenAndSpan { token, span } = self.lexer.next_token()?;
        match token {
            Token::IntegerLiteral(i) => Ok(ast::Expression::Literal(ast::Literal::IntLiteral(i))),
            Token::DoubleLiteral(d) => Ok(ast::Expression::Literal(ast::Literal::DoubleLiteral(d))),
            Token::BooleanLiteral(b) => {
                Ok(ast::Expression::Literal(ast::Literal::BooleanLiteral(b)))
            }
            Token::StringLiteral(s) => {
                // TODO parse string (escape, etc)
                let s = &s[1..s.len() - 1];
                let sid = self.string_interner.intern(s.to_string());
                Ok(ast::Expression::Literal(ast::Literal::StringLiteral(sid)))
            }
            Token::Minus => {
                let sub = self.parse_incdec_expression()?;
                Ok(ast::Expression::UnaryOperator {
                    unop: ast::UnaryOperatorKind::Minus,
                    sub: Box::new(sub),
                })
            }
            Token::Bang => {
                let sub = self.parse_incdec_expression()?;
                Ok(ast::Expression::UnaryOperator {
                    unop: ast::UnaryOperatorKind::LogicalNot,
                    sub: Box::new(sub),
                })
            }
            Token::LeftParenthesis => {
                let expr = self.parse_expression()?;
                expect!(self.lexer; Token::RightParenthesis, ")");
                Ok(expr)
            }
            Token::Identifier(id) => {
                let name = id.to_string();
                if let Token::LeftParenthesis = self.lexer.peek_token()?.token {
                    self.lexer.next_token()?;
                    let args = self.parse_expression_list()?;
                    expect!(self.lexer; Token::RightParenthesis, ")");
                    Ok(ast::Expression::FunctionCall {
                        function: name,
                        args,
                    })
                } else {
                    Ok(ast::Expression::Identifier(name))
                }
            }
            _ => {
                return_unexpected!("literal", "(", "-", "!", "identifier");
            }
        }
    }

    pub fn parse_expression_list(&mut self) -> ParsingResult<Vec<ast::Expression>> {
        let mut result = Vec::new();

        if let Token::RightParenthesis = self.lexer.peek_token()?.token {
            return Ok(result);
        }

        result.push(self.parse_expression()?);
        while let Token::Comma = self.lexer.peek_token()?.token {
            self.lexer.next_token()?;

            result.push(self.parse_expression()?);
        }

        Ok(result)
    }
}
