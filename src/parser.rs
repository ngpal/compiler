use std::iter::Peekable;

use crate::{
    error::{CompilerError, CompilerResult},
    lexer::{Lexer, Token, TokenKind},
};

pub enum Ast<'ip> {
    Identifier(Token<'ip>),
    Uint(Token<'ip>),
    UnaryOp {
        op: Token<'ip>,
        operand: Box<Ast<'ip>>,
    },
    BinaryOp {
        left: Box<Ast<'ip>>,
        op: Token<'ip>,
        right: Box<Ast<'ip>>,
    },
}

fn parse_binary_op<'ip, F>(
    lexer: &mut Peekable<Lexer<'ip>>,
    operators: &[TokenKind], // allowed binary operators
    subparser: F,            // function to parse the lower precedence expression
) -> CompilerResult<'ip, Ast<'ip>>
where
    F: Fn(&mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>>,
{
    let mut node = subparser(lexer)?; // parse left-hand side

    while let Some(Ok(tok)) =
        lexer.next_if(|tok| matches!(tok, Ok(x) if operators.contains(&x.kind)))
    {
        node = Ast::BinaryOp {
            left: Box::new(node),
            op: tok,
            right: Box::new(subparser(lexer)?), // parse right-hand side
        };
    }

    // If its peek is an err, propagate it
    if lexer.peek().is_some_and(|x| matches!(x, Err(_))) {
        lexer.next().unwrap()?;
    }

    Ok(node)
}

pub fn parse<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    expr(lexer)
}

fn expr<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    parse_binary_op(lexer, &[TokenKind::Plus, TokenKind::Minus], term)
}

fn term<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    parse_binary_op(lexer, &[TokenKind::Star, TokenKind::Slash], atom)
}

fn atom<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    // if lexer returns none, we have an unexpected EOF error
    let token = lexer.next().ok_or(CompilerError::UnexpectedEof)??;
    let node = match token.kind {
        TokenKind::Uint(_) => Ast::Uint(token),
        TokenKind::Identifier(_) => Ast::Identifier(token),
        TokenKind::Minus => Ast::UnaryOp {
            op: token,
            operand: Box::new(atom(lexer)?),
        },
        TokenKind::Lparen => {
            let node = expr(lexer)?;

            match lexer.next() {
                Some(Ok(tok)) if matches!(tok.kind, TokenKind::Rparen) => node,
                Some(Ok(got)) => return Err(CompilerError::UnexpectedToken { got, expected: ")" }),
                _ => return Err(CompilerError::UnexpectedEof),
            }
        }
        _ => {
            return Err(CompilerError::UnexpectedToken {
                got: token,
                expected: "num', '(', '-', 'ident",
            })
        }
    };

    Ok(node)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::{Lexer, TokenKind};
    use std::iter::Peekable;

    fn lex(input: &str) -> Peekable<Lexer> {
        Lexer::new(input).peekable()
    }

    #[test]
    fn test_parse_single_number() {
        let mut lexer = lex("42");
        let ast = parse(&mut lexer).unwrap();
        match ast {
            Ast::Uint(token) => assert_eq!(token.kind, TokenKind::Uint(42)),
            _ => panic!("expected Uint AST"),
        }
    }

    #[test]
    fn test_parse_identifier() {
        let mut lexer = lex("x");
        let ast = parse(&mut lexer).unwrap();
        match ast {
            Ast::Identifier(token) => assert_eq!(token.kind, TokenKind::Identifier("x".into())),
            _ => panic!("expected Identifier AST"),
        }
    }

    #[test]
    fn test_parse_simple_addition() {
        let mut lexer = lex("1 + 2");
        let ast = parse(&mut lexer).unwrap();
        match ast {
            Ast::BinaryOp { left, op, right } => {
                assert!(matches!(*left, Ast::Uint(_)));
                assert_eq!(op.kind, TokenKind::Plus);
                assert!(matches!(*right, Ast::Uint(_)));
            }
            _ => panic!("expected BinaryOp AST"),
        }
    }

    #[test]
    fn test_parse_unary_minus() {
        let mut lexer = lex("-5");
        let ast = parse(&mut lexer).unwrap();
        match ast {
            Ast::UnaryOp { op, operand } => {
                assert_eq!(op.kind, TokenKind::Minus);
                assert!(matches!(*operand, Ast::Uint(_)));
            }
            _ => panic!("expected UnaryOp AST"),
        }
    }

    #[test]
    fn test_parse_nested_expressions() {
        let mut lexer = lex("(1 + 2) * 3");
        let ast = parse(&mut lexer).unwrap();
        match ast {
            Ast::BinaryOp { left, op, right } => {
                assert_eq!(op.kind, TokenKind::Star);
                assert!(matches!(*right, Ast::Uint(_)));

                match *left {
                    Ast::BinaryOp { left, op, right } => {
                        assert!(matches!(*left, Ast::Uint(_)));
                        assert_eq!(op.kind, TokenKind::Plus);
                        assert!(matches!(*right, Ast::Uint(_)));
                    }
                    _ => panic!("expected BinaryOp for (1 + 2)"),
                }
            }
            _ => panic!("expected BinaryOp AST"),
        }
    }

    #[test]
    fn test_parse_missing_closing_paren() {
        let mut lexer = lex("(1 + 2");
        let result = parse(&mut lexer);
        assert!(matches!(result, Err(CompilerError::UnexpectedEof)));
    }

    #[test]
    fn test_parse_unexpected_token() {
        let mut lexer = lex("1 + * 2");
        let result = parse(&mut lexer);
        assert!(matches!(result, Err(CompilerError::UnexpectedToken { .. })));
    }
}
