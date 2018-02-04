use lexer::Token;
use parser::*;
use ast;
use codemap::{Span, Spanned};

#[derive(Debug, Clone, Copy)]
struct Infos {
    pub precedence: usize,
    pub right_assoc: bool,
    pub relational: bool,
}

fn info_of<'input>(binop: &Token<'input>) -> Option<Infos> {
    match *binop {
        Token::Equal => Some(Infos {
            precedence: 10,
            right_assoc: true,
            relational: false,
        }),
        Token::PipePipe => Some(Infos {
            precedence: 20,
            right_assoc: false,
            relational: false,
        }),
        Token::AmpAmp => Some(Infos {
            precedence: 30,
            right_assoc: false,
            relational: false,
        }),
        Token::EqualEqual | Token::BangEqual => Some(Infos {
            precedence: 40,
            right_assoc: false,
            relational: true,
        }),
        Token::Less | Token::Greater | Token::LessEqual | Token::GreaterEqual => Some(Infos {
            precedence: 50,
            right_assoc: false,
            relational: true,
        }),
        Token::Plus | Token::Minus => Some(Infos {
            precedence: 60,
            right_assoc: false,
            relational: false,
        }),
        Token::Star | Token::Slash | Token::Percent => Some(Infos {
            precedence: 70,
            right_assoc: false,
            relational: false,
        }),
        _ => None,
    }
}

fn apply(
    binop: &Token,
    lhs: Spanned<ast::Expression>,
    rhs: Spanned<ast::Expression>,
) -> ast::Expression {
    let lhs = Box::new(lhs);
    let rhs = Box::new(rhs);

    match *binop {
        Token::Equal => ast::Expression::Assign { lhs, rhs },
        Token::PipePipe => ast::Expression::LazyOperator {
            lazyop: ast::LazyOperatorKind::LogicalOr,
            lhs,
            rhs,
        },
        Token::AmpAmp => ast::Expression::LazyOperator {
            lazyop: ast::LazyOperatorKind::LogicalAnd,
            lhs,
            rhs,
        },
        Token::EqualEqual => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::Equal,
            lhs,
            rhs,
        },
        Token::BangEqual => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::NotEqual,
            lhs,
            rhs,
        },
        Token::Less => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::Less,
            lhs,
            rhs,
        },
        Token::LessEqual => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::LessEqual,
            lhs,
            rhs,
        },
        Token::Greater => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::Greater,
            lhs,
            rhs,
        },
        Token::GreaterEqual => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::GreaterEqual,
            lhs,
            rhs,
        },
        Token::Plus => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::Plus,
            lhs,
            rhs,
        },
        Token::Minus => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::Minus,
            lhs,
            rhs,
        },
        Token::Star => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::Multiply,
            lhs,
            rhs,
        },
        Token::Slash => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::Divide,
            lhs,
            rhs,
        },
        Token::Percent => ast::Expression::BinaryOperator {
            binop: ast::BinaryOperatorKind::Modulo,
            lhs,
            rhs,
        },
        _ => panic!("Expected an operator token"),
    }
}

pub(super) fn parse_expression_inner<'si, 'input>(
    parser: &mut Parser<'si, 'input>,
    lhs: Spanned<ast::Expression>,
    min_prec: usize,
) -> ParsingResult<Spanned<ast::Expression>> {
    let mut lhs = lhs;
    loop {
        if_chain! {
            if let Some(infos) = info_of(&parser.lexer.peek_token()?.inner);
            if (infos.precedence > min_prec)
                || (!infos.relational && infos.precedence == min_prec);
            then {
                let op = parser.lexer.next_token()?.inner;
                let mut rhs = parser.parse_cast_expression()?;

                loop {
                    if_chain! {
                        if let Some(next_infos) = info_of(&parser.lexer.peek_token()?.inner);
                        if (next_infos.precedence > infos.precedence)
                            || (next_infos.right_assoc
                                && next_infos.precedence == infos.precedence);
                        then {
                            // really unsure about infos or next_infos.precedenc
                            // rhs = parse_expression_inner(parser, rhs, infos.precedence)?;
                            // rhs = parse_expression_inner(parser, rhs, next_infos.precedence)?;
                            if next_infos.relational {
                                rhs = parse_expression_inner(parser, rhs, infos.precedence)?;
                            } else {
                                rhs = parse_expression_inner(parser, rhs, next_infos.precedence)?;
                            }
                        } else {
                            break
                        }
                    }
                }

                let span = Span::merge(lhs.span, rhs.span);
                lhs = Spanned::new(apply(&op, lhs, rhs), span);
            } else {
                break
            }
        }
    }
    Ok(lhs)
}
