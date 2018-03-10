use lexer::{Lexer, Token};
use ast;
use common;
use interner::Interner;
use codemap::{Span, Spanned};
use errors::ParsingError;

mod expression_parser;

use self::expression_parser::*;

pub type ParsingResult<T> = Result<T, Spanned<ParsingError>>;

pub fn parse_program(lexer: Lexer, strings: &mut Interner<String>) -> ParsingResult<ast::Program> {
    let declarations = {
        let mut parser = Parser::new(lexer, strings);

        let mut declarations = Vec::new();

        while !parser.at_eof()? {
            declarations.push(parser.parse_declaration()?);
        }
        declarations
    };

    Ok(ast::Program { declarations })
}

struct Parser<'si, 'input> {
    pub lexer: Lexer<'input>,
    pub string_interner: &'si mut Interner<String>,
}

macro_rules! accept {
    ($lexer:expr; $expect:pat => $ret:expr, $($expected:expr),*) => {
        {
            let Spanned { inner, span } = $lexer.next_token()?;
            if let $expect = inner {
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
    fn new(lexer: Lexer<'input>, string_interner: &'si mut Interner<String>) -> Self {
        Parser {
            lexer,
            string_interner,
        }
    }

    fn at_eof(&mut self) -> ParsingResult<bool> {
        if let Token::EOF = self.lexer.peek_token()?.inner {
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn parse_type(&mut self) -> ParsingResult<Spanned<ast::Type>> {
        match self.lexer.peek_token()?.inner {
            Token::Star => {
                let begin_span = self.lexer.next_token()?.span;
                let ty = self.parse_type()?;
                let span = Span::merge(begin_span, ty.span);
                Ok(Spanned::new(ast::Type::Pointer(Box::new(ty)), span))
            }
            Token::LeftSquare => {
                let begin_span = self.lexer.next_token()?.span;
                let ty = self.parse_type()?;
                expect!(self.lexer; Token::SemiColon, ";");
                let (size, _) =
                    accept!(self.lexer; Token::IntegerLiteral(lit) => lit as usize, "integer");
                let end_span = expect!(self.lexer; Token::RightSquare, "]");
                let span = Span::merge(begin_span, end_span);
                Ok(Spanned::new(ast::Type::Array(Box::new(ty), size), span))
            }
            Token::FnKeyword => {
                let begin_span = self.lexer.next_token()?.span;
                expect!(self.lexer; Token::LeftParenthesis, "(");
                let (parameters_ty, is_vararg) = self.parse_extern_parameter_list()?;
                expect!(self.lexer; Token::RightParenthesis, ")");
                expect!(self.lexer; Token::Arrow, "->");
                let return_ty = self.parse_type()?;
                let span = Span::merge(begin_span, return_ty.span);
                let func_ty = ast::FunctionType {
                    return_ty,
                    parameters_ty,
                    is_vararg,
                };
                Ok(Spanned::new(ast::Type::Function(Box::new(func_ty)), span))
            }
            Token::LeftParenthesis => {
                let begin_span = self.lexer.next_token()?.span;
                let types =
                    self.parse_comma_sep(&Token::RightParenthesis, Parser::parse_type, true)?;
                let end_span = expect!(self.lexer; Token::RightParenthesis, ")");
                let span = Span::merge(begin_span, end_span);
                let ty = if types.is_empty() {
                    ast::Type::Void
                } else {
                    ast::Type::Tuple(types)
                };
                Ok(Spanned::new(ty, span))
            }
            _ => {
                let (id, span) =
                    accept!(self.lexer; Token::Identifier(id) => id.to_owned(), "identifier");

                Ok(Spanned::new(ast::Type::Identifier(id), span))
            }
        }
    }

    fn parse_declaration(&mut self) -> ParsingResult<ast::Declaration> {
        let span = self.lexer.peek_token()?.span;
        match self.lexer.peek_token()?.inner {
            Token::StructKeyword => self.parse_struct_declaration(),
            Token::ExternKeyword => self.parse_extern_function_declaration(),
            Token::FnKeyword => self.parse_function_declaration(),
            _ => return_unexpected!(span, "struct", "typedef", "extern", "fn"),
        }
    }

    fn parse_struct_declaration(&mut self) -> ParsingResult<ast::Declaration> {
        let begin_span = expect!(self.lexer; Token::StructKeyword, "struct");
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::LeftBracket, "{");

        let fields = self.parse_comma_sep(&Token::RightBracket, Parser::parse_field, true)?;

        let end_span = expect!(self.lexer; Token::RightBracket, "}");
        let span = Span::merge(begin_span, end_span);

        Ok(ast::Declaration::Struct(ast::Struct { name, fields, span }))
    }

    fn parse_field(&mut self) -> ParsingResult<(Spanned<String>, Spanned<ast::Type>)> {
        let (name, span) =
            accept!(self.lexer; Token::Identifier(id) => id.to_string(), "identifier");
        let name = Spanned::new(name, span);
        expect!(self.lexer; Token::Colon, ":");
        let ty = self.parse_type()?;
        Ok((name, ty))
    }

    fn parse_extern_function_declaration(&mut self) -> ParsingResult<ast::Declaration> {
        let begin_span = expect!(self.lexer; Token::ExternKeyword, "extern");
        expect!(self.lexer; Token::FnKeyword, "fn");
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let (parameters, is_vararg) = self.parse_extern_parameter_list()?;
        expect!(self.lexer; Token::RightParenthesis, ")");

        let return_ty = if let Token::Arrow = self.lexer.peek_token()?.inner {
            self.lexer.next_token()?;
            self.parse_type()?
        } else {
            Spanned::new(ast::Type::Void, Span::dummy())
        };

        let end_span = expect!(self.lexer; Token::SemiColon, ";");
        let span = Span::merge(begin_span, end_span);

        Ok(ast::Declaration::ExternFunction(ast::ExternFunction {
            return_ty,
            name,
            parameters,
            is_vararg,
            span,
        }))
    }

    fn parse_extern_parameter_list(&mut self) -> ParsingResult<(Vec<Spanned<ast::Type>>, bool)> {
        // hard to change to parse_comma_sep
        let mut result = Vec::new();
        let mut is_vararg = false;

        if let Token::RightParenthesis = self.lexer.peek_token()?.inner {
            return Ok((result, is_vararg));
        }

        result.push(self.parse_type()?);
        while let Token::Comma = self.lexer.peek_token()?.inner {
            self.lexer.next_token()?;

            if let Token::DotDotDot = self.lexer.peek_token()?.inner {
                self.lexer.next_token()?;
                is_vararg = true;
                break;
            }
            result.push(self.parse_type()?);
        }

        Ok((result, is_vararg))
    }

    fn parse_function_declaration(&mut self) -> ParsingResult<ast::Declaration> {
        let begin_span = expect!(self.lexer; Token::FnKeyword, "fn");
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let parameters =
            self.parse_comma_sep(&Token::RightParenthesis, Parser::parse_parameter, true)?;
        let mut end_span = expect!(self.lexer; Token::RightParenthesis, ")");

        let return_ty = if let Token::Arrow = self.lexer.peek_token()?.inner {
            self.lexer.next_token()?;
            let ty = self.parse_type()?;
            end_span = ty.span;
            ty
        } else {
            Spanned::new(ast::Type::Void, Span::dummy())
        };

        let span = Span::merge(begin_span, end_span);
        let body = self.parse_block_statement()?.inner;

        Ok(ast::Declaration::Function(ast::Function {
            return_ty,
            name,
            parameters,
            body,
            span,
        }))
    }

    fn parse_parameter(&mut self) -> ParsingResult<(String, Spanned<ast::Type>)> {
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::Colon, ":");
        let ty = self.parse_type()?;
        Ok((name, ty))
    }

    fn parse_identifier(&mut self) -> ParsingResult<String> {
        let (id, _) = accept!(self.lexer; Token::Identifier(id) => id.to_string(), "identifier");
        Ok(id)
    }

    fn parse_block_statement(&mut self) -> ParsingResult<Spanned<ast::BlockStatement>> {
        let mut block = Vec::new();
        let begin_span = expect!(self.lexer; Token::LeftBracket, "{");
        loop {
            if let Token::RightBracket = self.lexer.peek_token()?.inner {
                break;
            }

            block.push(self.parse_statement()?);
        }
        let end_span = expect!(self.lexer; Token::RightBracket, "}");
        let span = Span::merge(begin_span, end_span);

        Ok(Spanned::new(ast::BlockStatement::from_vec(block), span))
    }

    fn parse_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        match self.lexer.peek_token()?.inner {
            Token::SemiColon => {
                let span = self.lexer.next_token()?.span;
                Ok(Spanned::new(ast::Statement::Empty, span))
            }
            Token::IfKeyword => self.parse_if_statement(),
            Token::WhileKeyword => self.parse_while_statement(),
            Token::ForKeyword => self.parse_for_statement(),
            Token::ReturnKeyword => self.parse_return_statement(),
            Token::LeftBracket => {
                let Spanned { inner: block, span } = self.parse_block_statement()?;
                let stmt = Spanned::new(ast::Statement::Block(block), span);
                Ok(stmt)
            }
            Token::BreakKeyword => {
                let span = self.lexer.next_token()?.span;
                Ok(Spanned::new(ast::Statement::Break, span))
            }
            Token::ContinueKeyword => {
                let span = self.lexer.next_token()?.span;
                Ok(Spanned::new(ast::Statement::Continue, span))
            }
            Token::LetKeyword => self.parse_let_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_expression_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        if let Token::SemiColon = self.lexer.peek_token()?.inner {
            let span = expect!(self.lexer; Token::SemiColon, ";");
            Ok(Spanned::new(ast::Statement::Empty, span))
        } else {
            let expr = self.parse_expression()?;
            let end_span = expect!(self.lexer; Token::SemiColon, ";");
            let span = Span::merge(expr.span, end_span);
            Ok(Spanned::new(ast::Statement::Expression(expr), span))
        }
    }

    fn parse_if_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let begin_span = expect!(self.lexer; Token::IfKeyword, "if");
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let condition = self.parse_expression()?;
        expect!(self.lexer; Token::RightParenthesis, ")");
        let body = Box::new(self.parse_statement()?);

        let else_clause = if let Token::ElseKeyword = self.lexer.peek_token()?.inner {
            self.lexer.next_token()?;
            let body = Box::new(self.parse_statement()?);
            Some(body)
        } else {
            None
        };

        let end_span = if let Some(ref e) = else_clause {
            e.span
        } else {
            body.span
        };
        let span = Span::merge(begin_span, end_span);

        Ok(Spanned::new(
            ast::Statement::If(ast::IfStatement {
                condition,
                body,
                else_clause,
            }),
            span,
        ))
    }

    fn parse_while_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let begin_span = expect!(self.lexer; Token::WhileKeyword, "while");
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let condition = self.parse_expression()?;
        expect!(self.lexer; Token::RightParenthesis, ")");
        let body = Box::new(self.parse_statement()?);

        let span = Span::merge(begin_span, body.span);

        Ok(Spanned::new(
            ast::Statement::While(ast::WhileStatement { condition, body }),
            span,
        ))
    }

    fn parse_for_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let begin_span = expect!(self.lexer; Token::ForKeyword, "for");
        expect!(self.lexer; Token::LeftParenthesis, "(");

        let init = if let Token::LetKeyword = self.lexer.peek_token()?.inner {
            self.parse_let_statement()?
        } else {
            self.parse_expression_statement()?
        };
        let init = Box::new(init);

        let condition = self.parse_expression()?;
        expect!(self.lexer; Token::SemiColon, ";");
        let step = if let Token::RightParenthesis = self.lexer.peek_token()?.inner {
            None
        } else {
            Some(self.parse_expression()?)
        };

        expect!(self.lexer; Token::RightParenthesis, ")");
        let body = Box::new(self.parse_statement()?);

        let span = Span::merge(begin_span, body.span);

        Ok(Spanned::new(
            ast::Statement::For(ast::ForStatement {
                init,
                condition,
                step,
                body,
            }),
            span,
        ))
    }

    fn parse_return_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let begin_span = expect!(self.lexer; Token::ReturnKeyword, "return");
        let expr = if let Token::SemiColon = self.lexer.peek_token()?.inner {
            None
        } else {
            Some(self.parse_expression()?)
        };
        let end_span = expect!(self.lexer; Token::SemiColon, ";");

        let span = Span::merge(begin_span, end_span);

        Ok(Spanned::new(ast::Statement::Return(expr), span))
    }

    fn parse_let_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let begin_span = expect!(self.lexer; Token::LetKeyword, "let");
        let name = self.parse_identifier()?;

        let ty = if let Token::Colon = self.lexer.peek_token()?.inner {
            self.lexer.next_token()?;
            Some(self.parse_type()?)
        } else {
            None
        };

        expect!(self.lexer; Token::Equal, "=");
        let value = self.parse_expression()?;

        let end_span = expect!(self.lexer; Token::SemiColon, ";");
        let span = Span::merge(begin_span, end_span);

        Ok(Spanned::new(
            ast::Statement::Let(ast::LetStatement { ty, name, value }),
            span,
        ))
    }

    fn parse_expression(&mut self) -> ParsingResult<Spanned<ast::Expression>> {
        let lhs = self.parse_cast_expression()?;
        parse_expression_inner(self, lhs, 0)
    }

    fn parse_cast_expression(&mut self) -> ParsingResult<Spanned<ast::Expression>> {
        let mut sub = self.parse_unop_expression()?;
        while let Token::AsKeyword = self.lexer.peek_token()?.inner {
            self.lexer.next_token()?;
            let ty = self.parse_type()?;
            let span = Span::merge(sub.span, ty.span);
            sub = Spanned::new(
                ast::Expression::Cast {
                    as_ty: ty,
                    sub: Box::new(sub),
                },
                span,
            );
        }
        Ok(sub)
    }

    fn parse_unop_expression(&mut self) -> ParsingResult<Spanned<ast::Expression>> {
        match self.lexer.peek_token()?.inner {
            Token::Minus => {
                let span = self.lexer.next_token()?.span;
                let sub = self.parse_unop_expression()?;
                let span = Span::merge(span, sub.span);
                let expr = ast::Expression::UnaryOperator {
                    unop: ast::UnaryOperatorKind::Minus,
                    sub: Box::new(sub),
                };
                Ok(Spanned::new(expr, span))
            }
            Token::Bang => {
                let span = self.lexer.next_token()?.span;
                let sub = self.parse_unop_expression()?;
                let span = Span::merge(span, sub.span);
                let expr = ast::Expression::UnaryOperator {
                    unop: ast::UnaryOperatorKind::LogicalNot,
                    sub: Box::new(sub),
                };
                Ok(Spanned::new(expr, span))
            }
            Token::Amp => {
                let span = self.lexer.next_token()?.span;
                let sub = self.parse_unop_expression()?;
                let span = Span::merge(span, sub.span);
                let expr = ast::Expression::LValueUnaryOperator {
                    lvalue_unop: ast::LValueUnaryOperatorKind::AddressOf,
                    sub: Box::new(sub),
                };
                Ok(Spanned::new(expr, span))
            }
            Token::Star => {
                let span = self.lexer.next_token()?.span;
                let sub = self.parse_unop_expression()?;
                let span = Span::merge(span, sub.span);
                let expr = ast::Expression::UnaryOperator {
                    unop: ast::UnaryOperatorKind::PtrDeref,
                    sub: Box::new(sub),
                };
                Ok(Spanned::new(expr, span))
            }
            _ => self.parse_mid_expression(),
        }
    }

    fn parse_mid_expression(&mut self) -> ParsingResult<Spanned<ast::Expression>> {
        let mut sub = self.parse_leaf_expression()?;
        loop {
            match self.lexer.peek_token()?.inner {
                Token::PlusPlus => {
                    let end_span = self.lexer.next_token()?.span;
                    let span = Span::merge(sub.span, end_span);
                    let expr = ast::Expression::LValueUnaryOperator {
                        lvalue_unop: ast::LValueUnaryOperatorKind::Increment,
                        sub: Box::new(sub),
                    };
                    sub = Spanned::new(expr, span);
                    continue;
                }
                Token::MinusMinus => {
                    let end_span = self.lexer.next_token()?.span;
                    let span = Span::merge(sub.span, end_span);
                    let expr = ast::Expression::LValueUnaryOperator {
                        lvalue_unop: ast::LValueUnaryOperatorKind::Decrement,
                        sub: Box::new(sub),
                    };
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
                Token::LeftParenthesis => {
                    self.lexer.next_token()?;
                    let args = self.parse_comma_sep(
                        &Token::RightParenthesis,
                        Parser::parse_expression,
                        true,
                    )?;
                    let end_span = expect!(self.lexer; Token::RightParenthesis, ")");
                    let span = Span::merge(sub.span, end_span);

                    let expr = ast::Expression::FunctionCall {
                        function: Box::new(sub),
                        args,
                    };

                    sub = Spanned::new(expr, span);
                    continue;
                }
                Token::Dot => {
                    self.lexer.next_token()?;
                    let (field, end_span) = match self.lexer.next_token()? {
                        Spanned {
                            span,
                            inner: Token::Identifier(id),
                        } => (common::Field::Named(id.to_string()), span),
                        Spanned {
                            span,
                            inner: Token::IntegerLiteral(i),
                        } => (common::Field::Index(i as _), span),
                        Spanned { span, .. } => {
                            return_unexpected!(span, "identifier", "int literal")
                        }
                    };

                    let span = Span::merge(sub.span, end_span);
                    let expr = ast::Expression::FieldAccess {
                        expr: Box::new(sub),
                        field,
                    };
                    sub = Spanned::new(expr, span);
                    continue;
                }
                _ => break,
            }
        }
        Ok(sub)
    }

    fn parse_leaf_expression(&mut self) -> ParsingResult<Spanned<ast::Expression>> {
        let Spanned { inner: token, span } = self.lexer.next_token()?;
        match token {
            Token::IntegerLiteral(i) => {
                let expr = ast::Expression::Literal(common::Literal::IntLiteral(i));
                Ok(Spanned::new(expr, span))
            }
            Token::DoubleLiteral(d) => {
                let expr = ast::Expression::Literal(common::Literal::DoubleLiteral(d));
                Ok(Spanned::new(expr, span))
            }
            Token::BooleanLiteral(b) => {
                let expr = ast::Expression::Literal(common::Literal::BooleanLiteral(b));
                Ok(Spanned::new(expr, span))
            }
            Token::StringLiteral(s) => {
                // TODO parse string (escape, etc)
                let s = &s[1..s.len() - 1];
                let s = convert_escape_string(s);
                let sid = self.string_interner.intern(s);
                let expr = ast::Expression::Literal(common::Literal::StringLiteral(sid));
                Ok(Spanned::new(expr, span))
            }
            Token::NullptrKeyword => Ok(Spanned::new(ast::Expression::Nullptr, span)),
            Token::LeftParenthesis => {
                let sub_expr = self.parse_expression()?;
                match self.lexer.peek_token()?.inner {
                    Token::Comma => {
                        self.lexer.next_token()?;

                        let mut values = vec![sub_expr];
                        values.extend(self.parse_comma_sep(
                            &Token::RightParenthesis,
                            Parser::parse_expression,
                            true,
                        )?);
                        let end_span = expect!(self.lexer; Token::RightParenthesis, ")");
                        let span = Span::merge(span, end_span);
                        let expr = ast::Expression::TupleLiteral { values };
                        Ok(Spanned::new(expr, span))
                    }
                    Token::RightParenthesis => {
                        let end_span = self.lexer.next_token()?.span;
                        let span = Span::merge(span, end_span);
                        let expr = ast::Expression::Parenthesis(Box::new(sub_expr));
                        Ok(Spanned::new(expr, span))
                    }
                    _ => return_unexpected!(span, ")", ","),
                }
            }
            Token::LeftSquare => {
                let first_value = self.parse_expression()?;
                let Spanned {
                    inner: next_token,
                    span: next_span,
                } = self.lexer.next_token()?;
                match next_token {
                    Token::RightSquare => {
                        let values = vec![first_value];
                        let span = Span::merge(span, next_span);
                        let expr = ast::Expression::ArrayLiteral { values };
                        Ok(Spanned::new(expr, span))
                    }
                    Token::Comma => {
                        let mut values = vec![first_value];
                        values.extend(self.parse_comma_sep(
                            &Token::RightSquare,
                            Parser::parse_expression,
                            false,
                        )?);
                        let end_span = expect!(self.lexer; Token::RightSquare, "]");
                        let span = Span::merge(span, end_span);
                        let expr = ast::Expression::ArrayLiteral { values };
                        Ok(Spanned::new(expr, span))
                    }
                    Token::SemiColon => {
                        let (size, _) = accept!(self.lexer; Token::IntegerLiteral(i) => i as usize, "integer literal");
                        let end_span = expect!(self.lexer; Token::RightSquare, "]");
                        let span = Span::merge(span, end_span);
                        let expr = ast::Expression::ArrayFillLiteral {
                            value: Box::new(first_value),
                            size,
                        };
                        Ok(Spanned::new(expr, span))
                    }
                    _ => return_unexpected!(span, ",", ";", "]"),
                }
            }
            Token::Identifier(id) => {
                let name = id.to_string();
                match self.lexer.peek_token()?.inner {
                    Token::LeftBracket => self.parse_struct_literal(name, span),
                    _ => {
                        let expr = ast::Expression::Identifier(name);
                        Ok(Spanned::new(expr, span))
                    }
                }
            }
            _ => {
                return_unexpected!(span, "literal", "(", "[", "identifier");
            }
        }
    }

    fn parse_struct_literal(
        &mut self,
        name: String,
        start_span: Span,
    ) -> ParsingResult<Spanned<ast::Expression>> {
        expect!(self.lexer; Token::LeftBracket, "{");
        let fields =
            self.parse_comma_sep(&Token::RightBracket, Parser::parse_field_literal, false)?; // do we allow zero fields struct ?
        let end_span = expect!(self.lexer; Token::RightBracket, "}");
        let span = Span::merge(start_span, end_span);
        let expr = ast::Expression::StructLiteral {
            struct_name: name,
            fields,
        };
        Ok(Spanned::new(expr, span))
    }

    #[inline]
    fn parse_comma_sep<F, T>(
        &mut self,
        stop: &Token<'input>,
        step: F,
        zero: bool,
    ) -> ParsingResult<Vec<T>>
    where
        F: Fn(&mut Self) -> ParsingResult<T>,
    {
        let mut result = Vec::new();

        if zero && stop == &self.lexer.peek_token()?.inner {
            return Ok(result);
        }

        result.push(step(self)?);
        while let Token::Comma = self.lexer.peek_token()?.inner {
            self.lexer.next_token()?;
            if stop == &self.lexer.peek_token()?.inner {
                break;
            }

            result.push(step(self)?);
        }

        Ok(result)
    }

    fn parse_field_literal(
        &mut self,
    ) -> ParsingResult<(Spanned<String>, Spanned<ast::Expression>)> {
        let (name, span) =
            accept!(self.lexer; Token::Identifier(id) => id.to_string(), "identifier");

        let name = Spanned::new(name, span);
        expect!(self.lexer; Token::Colon, ":");
        let field_expr = self.parse_expression()?;
        Ok((name, field_expr))
    }
}

fn convert_escape_string(s: &str) -> String {
    let mut iter = s.chars();
    let mut output = String::new();

    while let Some(c) = iter.next() {
        if c != '\\' {
            output.push(c);
            continue;
        }

        match iter.next() {
            Some('b') => output.push('\u{0008}'),
            Some('f') => output.push('\u{000C}'),
            Some('n') => output.push('\n'),
            Some('r') => output.push('\r'),
            Some('t') => output.push('\t'),
            Some('\'') => output.push('\''),
            Some('\"') => output.push('\"'),
            Some('\\') => output.push('\\'),
            _ => panic!("Uncatched unterminated escape in string literal"),
        };
    }
    output
}
