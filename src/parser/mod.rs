use lexer::{Lexer, Token, TokenAndSpan};
use ast;
use ty;
use string_interner::StringInterner;
use span::{Span, Spanned};

mod parsing_error;
mod expression_parser;

pub use self::parsing_error::{ParsingResult, ParsingError};
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
                return_unexpected!(span, $($expected),*);
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
    ($span:expr, $($expected:expr),*) => {
        return Err(Spanned::new(
            ParsingError::Unexpected(vec![$($expected.into()),*]),
            $span
        ));
    }
}

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

    pub fn parse_builtin_type(&mut self, void: bool) -> ParsingResult<Spanned<ty::Type>> {
        let TokenAndSpan { token, span } = self.lexer.next_token()?;
        let ty = match token {
            Token::IntKeyword => ty::Type::Int,
            Token::DoubleKeyword => ty::Type::Double,
            Token::BooleanKeyword => ty::Type::Boolean,
            Token::VoidKeyword if void => ty::Type::Void,
            _ => {
                if void {
                    return_unexpected!(span, "int", "boolean", "double", "void")
                } else {
                    return_unexpected!(span, "int", "boolean", "double", "void")
                }
            }
        };

        Ok(Spanned::new(ty, span))
    }

    pub fn parse_type(&mut self, void: bool) -> ParsingResult<Spanned<ty::Type>> {
        let Spanned { inner: mut ty, mut span } = self.parse_builtin_type(void)?;

        while let Token::LeftSquare = self.lexer.peek_token()?.token {
            self.lexer.next_token()?;
            let end_span = expect!(self.lexer; Token::RightSquare, "]");
            span = Span::merge(span, end_span);
            ty = ty::Type::Array(Box::new(ty));
        }

        Ok(Spanned::new(ty, span))
    }

    pub fn parse_function_declaration(&mut self) -> ParsingResult<ast::Function> {
        let Spanned { inner: return_ty, span: ty_span } = self.parse_type(true)?;
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
        let ty = self.parse_type(false)?.inner;
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
    ) -> ParsingResult<(String, Option<Spanned<ast::Expression>>)> {
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
        let Spanned { inner: ty, span: ty_span } = self.parse_type(false)?;
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

    pub fn parse_expression(&mut self) -> ParsingResult<Spanned<ast::Expression>> {
        let lhs = self.parse_mid_expression()?;
        parse_expression_inner(self, lhs, 0)
    }

    pub fn parse_mid_expression(&mut self) -> ParsingResult<Spanned<ast::Expression>> {
        let mut sub = self.parse_leaf_expression()?;
        loop {
            match self.lexer.peek_token()?.token {
                Token::PlusPlus => {
                    let end_span = self.lexer.next_token()?.span;
                    let span = Span::merge(sub.span, end_span);
                    let expr = ast::Expression::Increment(Box::new(sub));
                    sub = Spanned::new(expr, span);
                    continue;
                }
                Token::MinusMinus => {
                    let end_span = self.lexer.next_token()?.span;
                    let span = Span::merge(sub.span, end_span);
                    let expr = ast::Expression::Decrement(Box::new(sub));
                    sub = Spanned::new(expr, span);
                    continue;
                }
                Token::LeftSquare => {
                    self.lexer.next_token()?;
                    let index_expr = self.parse_expression()?;
                    let end_span = expect!(self.lexer; Token::RightSquare, "]");
                    let span = Span::merge(sub.span, end_span);
                    let expr = ast::Expression::Subscript {
                        array: Box::new(sub),
                        index: Box::new(index_expr),
                    };
                    sub = Spanned::new(expr, span);
                    continue;
                }
                _ => break,
            }
        }
        Ok(sub)
    }

    pub fn parse_leaf_expression(&mut self) -> ParsingResult<Spanned<ast::Expression>> {
        let TokenAndSpan { token, span } = self.lexer.next_token()?;
        match token {
            Token::IntegerLiteral(i) => {
                let expr = ast::Expression::Literal(ast::Literal::IntLiteral(i));
                Ok(Spanned::new(expr, span))
            },
            Token::DoubleLiteral(d) => {
                let expr = ast::Expression::Literal(ast::Literal::DoubleLiteral(d));
                Ok(Spanned::new(expr, span))
            } 
            Token::BooleanLiteral(b) => {
                let expr = ast::Expression::Literal(ast::Literal::BooleanLiteral(b));
                Ok(Spanned::new(expr, span))
            }
            Token::StringLiteral(s) => {
                // TODO parse string (escape, etc)
                let s = &s[1..s.len() - 1];
                let sid = self.string_interner.intern(s.to_string());
                let expr = ast::Expression::Literal(ast::Literal::StringLiteral(sid));
                Ok(Spanned::new(expr, span))
            }
            Token::NewKeyword => {
                let Spanned { inner: bty, mut span } = self.parse_builtin_type(false)?;
                let mut sizes = Vec::new();
                loop {
                    expect!(self.lexer; Token::LeftSquare, "[");
                    let size = accept!(self.lexer; Token::IntegerLiteral(i) => i as usize, "integer").0;
                    sizes.push(size);
                    span = Span::merge(span, expect!(self.lexer; Token::RightSquare, "]"));

                    if let Token::LeftSquare = self.lexer.peek_token()?.token {
                        continue
                    } else {
                        break
                    }
                }
                
                Ok(Spanned::new(
                    ast::Expression::NewArray {
                        ty: bty,
                        sizes
                    },
                    span
                ))
            }
            Token::Minus => {
                let sub = self.parse_mid_expression()?;
                let span = Span::merge(span, sub.span);
                let expr = ast::Expression::UnaryOperator {
                    unop: ast::UnaryOperatorKind::Minus,
                    sub: Box::new(sub),
                };
                Ok(Spanned::new(expr, span))
            }
            Token::Bang => {
                let sub = self.parse_mid_expression()?;
                let span = Span::merge(span, sub.span);
                let expr = ast::Expression::UnaryOperator {
                    unop: ast::UnaryOperatorKind::LogicalNot,
                    sub: Box::new(sub),
                };
                Ok(Spanned::new(expr, span))
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
                    let end_span = expect!(self.lexer; Token::RightParenthesis, ")");
                    let span = Span::merge(span, end_span);
                    let expr = ast::Expression::FunctionCall {
                        function: name,
                        args,
                    };
                    Ok(Spanned::new(expr, span))
                } else {
                    let expr = ast::Expression::Identifier(name);
                    Ok(Spanned::new(expr, span))
                }
            }
            _ => {
                return_unexpected!(span, "literal", "(", "-", "!", "identifier");
            }
        }
    }

    pub fn parse_expression_list(&mut self) -> ParsingResult<Vec<Spanned<ast::Expression>>> {
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
