use std::iter::Peekable;

use crate::{
    error::{CompilerError, CompilerResult},
    lexer::{Lexer, Token, TokenKind},
};

#[derive(Debug)]
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
    Func {
        ident: Box<Ast<'ip>>,
        param: Box<Ast<'ip>>,
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

    if let Some(Err(_)) = lexer.peek() {
        lexer.next().unwrap()?; // propagate error
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
        TokenKind::Identifier(_) => {
            let mut node = Ast::Identifier(token);

            if let Some(Ok(_)) =
                lexer.next_if(|x| matches!(x, Ok(x) if matches!(x.kind, TokenKind::Lparen)))
            {
                let param = expr(lexer)?;

                match lexer.next() {
                    Some(Ok(tok)) if matches!(tok.kind, TokenKind::Rparen) => {}
                    Some(Ok(got)) => {
                        return Err(CompilerError::UnexpectedToken { got, expected: ")" })
                    }
                    _ => return Err(CompilerError::UnexpectedEof),
                };

                node = Ast::Func {
                    ident: Box::new(node),
                    param: Box::new(param),
                };
            }

            node
        }
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
                expected: "uint', '(', '-', 'ident",
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

    fn lex(input: &str) -> Peekable<Lexer<'_>> {
        Lexer::new(input).peekable()
    }

    fn assert_uint(ast: &Ast<'_>, expected: u32) {
        match ast {
            Ast::Uint(token) => assert_eq!(token.kind, TokenKind::Uint(expected)),
            _ => panic!("expected Uint({}), got {:?}", expected, ast),
        }
    }

    fn assert_identifier(ast: &Ast<'_>, expected: &str) {
        match ast {
            Ast::Identifier(token) => {
                assert_eq!(token.kind, TokenKind::Identifier(expected.into()))
            }
            _ => panic!("expected Identifier({}), got {:?}", expected, ast),
        }
    }

    fn assert_binary_op<'a>(ast: &'a Ast<'a>, op_kind: TokenKind) -> (&'a Ast<'a>, &'a Ast<'a>) {
        match ast {
            Ast::BinaryOp { left, op, right } => {
                assert_eq!(
                    op.kind, op_kind,
                    "expected {:?}, got {:?}",
                    op_kind, op.kind
                );
                (left, right)
            }
            _ => panic!("expected BinaryOp({:?}), got {:?}", op_kind, ast),
        }
    }

    fn assert_unary_op<'a>(ast: &'a Ast<'a>, op_kind: TokenKind) -> &'a Ast<'a> {
        match ast {
            Ast::UnaryOp { op, operand } => {
                assert_eq!(
                    op.kind, op_kind,
                    "expected {:?}, got {:?}",
                    op_kind, op.kind
                );
                operand
            }
            _ => panic!("expected UnaryOp({:?}), got {:?}", op_kind, ast),
        }
    }

    #[test]
    fn test_parse_single_number() {
        let mut lexer = lex("42");
        let ast = parse(&mut lexer).unwrap();
        assert_uint(&ast, 42);
    }

    #[test]
    fn test_parse_identifier() {
        let mut lexer = lex("x");
        let ast = parse(&mut lexer).unwrap();
        assert_identifier(&ast, "x");
    }

    #[test]
    fn test_parse_simple_addition() {
        let mut lexer = lex("1 + 2");
        let ast = parse(&mut lexer).unwrap();
        let (left, right) = assert_binary_op(&ast, TokenKind::Plus);
        assert_uint(left, 1);
        assert_uint(right, 2);
    }

    #[test]
    fn test_parse_unary_minus() {
        let mut lexer = lex("-5");
        let ast = parse(&mut lexer).unwrap();
        let operand = assert_unary_op(&ast, TokenKind::Minus);
        assert_uint(operand, 5);
    }

    #[test]
    fn test_parse_nested_expressions() {
        let mut lexer = lex("(1 + 2) * 3");
        let ast = parse(&mut lexer).unwrap();

        let (left, right) = assert_binary_op(&ast, TokenKind::Star);
        assert_uint(right, 3);

        let (nested_left, nested_right) = assert_binary_op(left, TokenKind::Plus);
        assert_uint(nested_left, 1);
        assert_uint(nested_right, 2);
    }

    #[test]
    fn test_parse_function_call() {
        let mut lexer = lex("foo(42)");
        let ast = parse(&mut lexer).unwrap();
        match ast {
            Ast::Func { ident, param } => {
                assert_identifier(&ident, "foo");
                assert_uint(&param, 42);
            }
            _ => panic!("expected Func, got {:?}", ast),
        }
    }

    #[test]
    fn test_parse_missing_closing_paren() {
        let mut lexer = lex("(1 + 2");
        let result = parse(&mut lexer);
        assert!(
            matches!(result, Err(CompilerError::UnexpectedEof)),
            "expected UnexpectedEof"
        );
    }

    #[test]
    fn test_parse_unexpected_token() {
        let mut lexer = lex("1 + * 2");
        let result = parse(&mut lexer);
        assert!(
            matches!(result, Err(CompilerError::UnexpectedToken { .. })),
            "expected UnexpectedToken"
        );
    }

    #[test]
    fn test_parse_function_call_missing_paren() {
        let mut lexer = lex("foo(42");
        let result = parse(&mut lexer);
        assert!(
            matches!(result, Err(CompilerError::UnexpectedEof)),
            "expected UnexpectedEof due to missing `)`"
        );
    }

    #[test]
    fn test_parse_chained_operations() {
        let mut lexer = lex("1 + 2 * 3");
        let ast = parse(&mut lexer).unwrap();

        let (left, right) = assert_binary_op(&ast, TokenKind::Plus);
        assert_uint(left, 1);

        let (mul_left, mul_right) = assert_binary_op(right, TokenKind::Star);
        assert_uint(mul_left, 2);
        assert_uint(mul_right, 3);
    }
}
