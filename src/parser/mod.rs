use lexer::{Lexer, Token, TokenAndSpan};
use ast;
use ty;
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
    fn new(lexer: Lexer<'input>, string_interner: &'si mut Interner<String>) -> Self {
        Parser {
            lexer,
            string_interner,
        }
    }

    fn at_eof(&mut self) -> ParsingResult<bool> {
        if let Token::EOF = self.lexer.peek_token()?.token {
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn parse_bottom_type(&mut self) -> ParsingResult<Spanned<ty::Type>> {
        let TokenAndSpan { token, span } = self.lexer.next_token()?;
        let ty = match token {
            Token::IntKeyword => ty::Type::Int,
            Token::DoubleKeyword => ty::Type::Double,
            Token::BooleanKeyword => ty::Type::Boolean,
            Token::StringKeyword => ty::Type::String,
            Token::VoidKeyword => ty::Type::Void,
            Token::Identifier(id) => ty::Type::StructPointer(id.to_string()),
            _ => return_unexpected!(span, "int", "boolean", "double", "void"),
        };

        Ok(Spanned::new(ty, span))
    }

    fn parse_type_inner(&mut self) -> ParsingResult<Spanned<ty::Type>> {
        let Spanned {
            inner: mut ty,
            mut span,
        } = self.parse_bottom_type()?;

        loop {
            match self.lexer.peek_token()?.token {
                Token::LeftSquare => {
                    self.lexer.next_token()?;
                    let end_span = expect!(self.lexer; Token::RightSquare, "]");
                    span = Span::merge(span, end_span);
                    ty = ty::Type::Array(Box::new(ty));
                }
                Token::Star => {
                    let end_span = self.lexer.next_token()?.span;
                    span = Span::merge(span, end_span);
                    ty = ty::Type::Pointer(Box::new(ty));
                }
                _ => break,
            }
        }

        Ok(Spanned::new(ty, span))
    }

    fn parse_type(&mut self, void: bool) -> ParsingResult<Spanned<ty::Type>> {
        let Spanned { inner: ty, span } = self.parse_type_inner()?;
        if !void && ty == ty::Type::Void {
            panic!()
        } else if ty.is_invalid() {
            panic!()
        }
        Ok(Spanned::new(ty, span))
    }

    fn parse_declaration(&mut self) -> ParsingResult<ast::Declaration> {
        match self.lexer.peek_token()?.token {
            Token::StructKeyword => self.parse_struct_declaration(),
            Token::TypedefKeyword => self.parse_typedef_declaration(),
            Token::ExternKeyword => self.parse_extern_function_declaration(),
            _ => self.parse_function_declaration(),
        }
    }

    fn parse_typedef_declaration(&mut self) -> ParsingResult<ast::Declaration> {
        expect!(self.lexer; Token::TypedefKeyword, "typedef");
        expect!(self.lexer; Token::StructKeyword, "struct");
        let struct_name = self.parse_identifier()?;
        expect!(self.lexer; Token::Star, "*");
        let ptr_name = self.parse_identifier()?;
        expect!(self.lexer; Token::SemiColon, ";");

        Ok(ast::Declaration::Typedef(ast::Typedef {
            struct_name,
            ptr_name,
        }))
    }

    fn parse_struct_declaration(&mut self) -> ParsingResult<ast::Declaration> {
        let begin_span = expect!(self.lexer; Token::StructKeyword, "struct");
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::LeftBracket, "{");

        let mut fields = Vec::new();
        loop {
            if let Token::RightBracket = self.lexer.peek_token()?.token {
                break;
            }

            fields.push(self.parse_field()?);
        }

        expect!(self.lexer; Token::RightBracket, "}");
        let end_span = expect!(self.lexer; Token::SemiColon, ";");

        let span = Span::merge(begin_span, end_span);

        Ok(ast::Declaration::Struct(ast::Struct { name, fields, span }))
    }

    fn parse_field(&mut self) -> ParsingResult<(ty::Type, String)> {
        let Spanned { inner: ty, .. } = self.parse_type(false)?;
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::SemiColon, ";");
        Ok((ty, name))
    }

    fn parse_extern_function_declaration(&mut self) -> ParsingResult<ast::Declaration> {
        let begin_span = expect!(self.lexer; Token::ExternKeyword, "extern");
        let return_ty = self.parse_type(true)?.inner;
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let (parameters, is_vararg) = self.parse_extern_parameter_list()?;
        expect!(self.lexer; Token::RightParenthesis, ")");
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

    fn parse_extern_parameter_list(&mut self) -> ParsingResult<(Vec<ty::Type>, bool)> {
        let mut result = Vec::new();
        let mut is_vararg = false;

        if let Token::RightParenthesis = self.lexer.peek_token()?.token {
            return Ok((result, is_vararg));
        }

        result.push(self.parse_type(false)?.inner);
        while let Token::Comma = self.lexer.peek_token()?.token {
            self.lexer.next_token()?;

            if let Token::DotDotDot = self.lexer.peek_token()?.token {
                self.lexer.next_token()?;
                is_vararg = true;
                break;
            }
            result.push(self.parse_type(false)?.inner);
        }

        Ok((result, is_vararg))
    }

    fn parse_function_declaration(&mut self) -> ParsingResult<ast::Declaration> {
        let Spanned {
            inner: return_ty,
            span: ty_span,
        } = self.parse_type(true)?;
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::LeftParenthesis, "(");
        let parameters = self.parse_parameter_list()?;
        let end_span = expect!(self.lexer; Token::RightParenthesis, ")");
        let Spanned { inner: body, .. } = self.parse_block_statement()?;

        let span = Span::merge(ty_span, end_span);

        Ok(ast::Declaration::Function(ast::Function {
            return_ty,
            name,
            parameters,
            body,
            span,
        }))
    }

    fn parse_parameter_list(&mut self) -> ParsingResult<Vec<(ty::Type, String)>> {
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

    fn parse_parameter(&mut self) -> ParsingResult<(ty::Type, String)> {
        let ty = self.parse_type(false)?.inner;
        let name = self.parse_identifier()?;
        Ok((ty, name))
    }

    fn parse_identifier(&mut self) -> ParsingResult<String> {
        let (id, _) = accept!(self.lexer; Token::Identifier(id) => id.to_string(), "identifier");
        Ok(id)
    }

    fn parse_block_statement(&mut self) -> ParsingResult<Spanned<ast::BlockStatement>> {
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

    fn parse_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        match self.lexer.peek_token()?.token {
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
            Token::IntKeyword | Token::DoubleKeyword | Token::BooleanKeyword => {
                self.parse_var_declaration()
            }
            _ => {
                let state = self.lexer.save_state();
                if let Ok(stmt) = self.parse_expression_statement() {
                    Ok(stmt)
                } else {
                    self.lexer.load_state(state);
                    self.parse_var_declaration()
                }
            }
        }
    }

    fn parse_expression_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let expr = self.parse_expression()?;
        let end_span = expect!(self.lexer; Token::SemiColon, ";");
        let span = Span::merge(expr.span, end_span);
        Ok(Spanned::new(ast::Statement::Expression(expr), span))
    }

    fn parse_if_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
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
        let ty = self.parse_type(false)?.inner;
        let name = self.parse_identifier()?;
        expect!(self.lexer; Token::Colon, ":");
        let array = self.parse_expression()?;
        expect!(self.lexer; Token::RightParenthesis, ")");
        let body = Box::new(self.parse_statement()?);

        let span = Span::merge(begin_span, body.span);

        Ok(Spanned::new(
            ast::Statement::For(ast::ForStatement {
                ty,
                name,
                array,
                body,
            }),
            span,
        ))
    }

    fn parse_return_statement(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
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

    fn parse_identifier_and_maybe_value(
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

    fn parse_var_declaration(&mut self) -> ParsingResult<Spanned<ast::Statement>> {
        let Spanned {
            inner: ty,
            span: ty_span,
        } = self.parse_type(false)?;
        let mut declarations = Vec::new();

        declarations.push(self.parse_identifier_and_maybe_value()?);
        while let Token::Comma = self.lexer.peek_token()?.token {
            self.lexer.next_token()?;
            declarations.push(self.parse_identifier_and_maybe_value()?);
        }
        let end_span = expect!(self.lexer; Token::SemiColon, ";");

        let span = Span::merge(ty_span, end_span);

        Ok(Spanned::new(
            ast::Statement::VarDecl(ast::VarDeclarations { ty, declarations }),
            span,
        ))
    }

    fn parse_expression(&mut self) -> ParsingResult<Spanned<ast::Expression>> {
        let lhs = self.parse_mid_expression()?;
        parse_expression_inner(self, lhs, 0)
    }

    fn parse_mid_expression(&mut self) -> ParsingResult<Spanned<ast::Expression>> {
        let mut sub = self.parse_leaf_expression()?;
        loop {
            match self.lexer.peek_token()?.token {
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
                Token::Dot => {
                    self.lexer.next_token()?;
                    let (member, end_span) =
                        accept!(self.lexer; Token::Identifier(id) => id.to_string(), "identifier");
                    let span = Span::merge(sub.span, end_span);
                    let expr = ast::Expression::MemberAccess {
                        expr: Box::new(sub),
                        member,
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
        let TokenAndSpan { token, span } = self.lexer.next_token()?;
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
            Token::NewKeyword => {
                let Spanned {
                    inner: bty,
                    mut span,
                } = self.parse_bottom_type()?;
                let mut sizes = Vec::new();
                loop {
                    expect!(self.lexer; Token::LeftSquare, "[");
                    let size = self.parse_expression()?;
                    sizes.push(size);
                    span = Span::merge(span, expect!(self.lexer; Token::RightSquare, "]"));

                    if let Token::LeftSquare = self.lexer.peek_token()?.token {
                        continue;
                    } else {
                        break;
                    }
                }

                Ok(Spanned::new(
                    ast::Expression::NewArray { ty: bty, sizes },
                    span,
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
            Token::Amp => {
                let sub = self.parse_mid_expression()?;
                let span = Span::merge(span, sub.span);
                let expr = ast::Expression::LValueUnaryOperator {
                    lvalue_unop: ast::LValueUnaryOperatorKind::AddressOf,
                    sub: Box::new(sub),
                };
                Ok(Spanned::new(expr, span))
            }
            Token::Star => {
                let sub = self.parse_mid_expression()?;
                let span = Span::merge(span, sub.span);
                let expr = ast::Expression::UnaryOperator {
                    unop: ast::UnaryOperatorKind::PtrDeref,
                    sub: Box::new(sub),
                };
                Ok(Spanned::new(expr, span))
            }
            Token::LeftParenthesis => {
                let sub_expr = self.parse_expression()?;
                let end_span = expect!(self.lexer; Token::RightParenthesis, ")");
                let span = Span::merge(span, end_span);
                let expr = ast::Expression::Parenthesis(Box::new(sub_expr));
                Ok(Spanned::new(expr, span))
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

    fn parse_expression_list(&mut self) -> ParsingResult<Vec<Spanned<ast::Expression>>> {
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
