use crate::{lexer::TokenKind, parser::Ast};

#[derive(Debug, Clone, Copy)]
pub enum Data {
    LitInt(i32),
    MemInt(u64),
}

pub fn gen(ast: Ast) -> String {
    match ast {
        Ast::BinaryOp { left, op, right } => {
            let left = eval(*left);
            let right = eval(*right);

            match op.kind {
                TokenKind::Plus => handle_add(left, right),
                _ => unimplemented!("binary op {:?} not implemented", op.kind),
            }
        }
        _ => unimplemented!("gen not implemented for {:?}", ast),
    }
}

pub fn handle_add(left: Data, right: Data) -> String {
    use Data::*;
    match (left, right) {
        (LitInt(num1), LitInt(num2)) => format!("mov w0, {}\n", num1 + num2),
        _ => unimplemented!(
            "unimplented pattern for bin op add {:?} and {:?}",
            left,
            right
        ),
    }
}

pub fn eval(ast: Ast) -> Data {
    match ast {
        Ast::Uint(tok) => {
            let TokenKind::Uint(num) = tok.kind else {
                unreachable!("Found {:?} token in an Uint node", tok);
            };
            Data::LitInt(num as i32)
        }
        _ => unimplemented!("eval not implemented for {:?}", ast),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::{Slice, Token, TokenKind};
    use crate::parser::Ast;

    #[test]
    fn test_literal_addition() {
        let input = "3+5";

        let left = Ast::Uint(Token::new(TokenKind::Uint(3), Slice::new(0, 1, input)));
        let right = Ast::Uint(Token::new(TokenKind::Uint(5), Slice::new(2, 1, input)));
        let ast = Ast::BinaryOp {
            left: Box::new(left),
            op: Token::new(TokenKind::Plus, Slice::new(1, 1, input)),
            right: Box::new(right),
        };

        let result = gen(ast);
        assert_eq!(result, "mov w0, 8\n");
    }
}
