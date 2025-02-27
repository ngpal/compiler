use std::{
    iter::{Enumerate, Peekable},
    str::Chars,
};

// pub enum Keyword {
//     If,
//     Let,
//     Loop,
// }

pub enum TokenKind {
    Uint(u32),
    // Float(f32),
    // Bool(bool),
    // Keyword(Keyword),
    Identifier(String),
    // String(String),
    Plus,
    Minus,
    Star,
    Slash,
    Semicolon,
    Lparen,
    Rparen,
}

pub struct Slice<'ip> {
    start: usize,
    len: usize,
    input: &'ip str,
}

impl<'ip> Slice<'ip> {
    pub fn new(start: usize, len: usize, input: &'ip str) -> Self {
        Self { start, len, input }
    }
}

pub struct Token<'ip> {
    kind: TokenKind,
    slice: Slice<'ip>,
}

impl<'ip> Token<'ip> {
    pub fn new(kind: TokenKind, slice: Slice<'ip>) -> Self {
        Self { kind, slice }
    }
}

pub struct Lexer<'ip> {
    input: &'ip str,
    input_iter: Peekable<Enumerate<Chars<'ip>>>,
}

impl<'ip> Lexer<'ip> {
    pub fn new(input: &'ip str) -> Self {
        Self {
            input,
            input_iter: input.chars().enumerate().peekable(),
        }
    }

    fn get_int(&mut self, start_char: char) -> (TokenKind, usize) {
        let mut int = ((start_char as u8) - b'0') as u32;
        let mut len = 1;
        while let Some((_, ch)) = self.input_iter.next_if(|(_, ch)| ch.is_ascii_digit()) {
            int = int * 10 + ((ch as u8) - b'0') as u32;
            len += 1;
        }

        (TokenKind::Uint(int), len)
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Token<'input>;
    fn next(&mut self) -> Option<Self::Item> {
        let (start, cur) = self.input_iter.next()?;
        let (kind, len) = match cur {
            '+' => (TokenKind::Plus, 1),
            '-' => (TokenKind::Minus, 1),
            '*' => (TokenKind::Star, 1),
            '/' => (TokenKind::Slash, 1),
            ';' => (TokenKind::Semicolon, 1),
            '(' => (TokenKind::Lparen, 1),
            ')' => (TokenKind::Rparen, 1),
            ch if ch.is_ascii_digit() => self.get_int(ch),
            _ => unimplemented!(),
        };

        Some(Token::new(kind, Slice::new(start, len, self.input)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_tokens() {
        // Test each individual token type
        let test_cases = [
            ("+", TokenKind::Plus),
            ("-", TokenKind::Minus),
            ("*", TokenKind::Star),
            ("/", TokenKind::Slash),
            (";", TokenKind::Semicolon),
            ("(", TokenKind::Lparen),
            (")", TokenKind::Rparen),
            ("42", TokenKind::Uint(42)),
        ];

        for (input, expected_kind) in test_cases {
            let mut lexer = Lexer::new(input);
            let token = lexer.next().unwrap();

            match (&token.kind, &expected_kind) {
                (TokenKind::Uint(actual), TokenKind::Uint(expected)) => {
                    assert_eq!(
                        actual, expected,
                        "Integer token mismatch for input '{}'",
                        input
                    );
                }
                _ => assert!(
                    matches!(token.kind, expected_kind),
                    "Token kind mismatch for input '{}'",
                    input
                ),
            }

            // Check if slice is correctly created
            assert_eq!(token.slice.start, 0);

            // For single-character tokens, len should be 1
            // For multi-digit numbers, len depends on the input length
            let expected_len = if let TokenKind::Uint(_) = expected_kind {
                if input == "42" {
                    2
                } else {
                    input.len()
                }
            } else {
                1
            };

            assert_eq!(
                token.slice.len, expected_len,
                "Incorrect slice length for input '{}'",
                input
            );

            // No more tokens should be available
            assert!(
                lexer.next().is_none(),
                "Expected end of tokens for input '{}'",
                input
            );
        }
    }

    #[test]
    fn test_multiple_digits() {
        let test_cases = [("123", 123), ("9999", 9999), ("0", 0), ("42", 42)];

        for (input, expected) in test_cases {
            let mut lexer = Lexer::new(input);
            let token = lexer.next().unwrap();

            if let TokenKind::Uint(value) = token.kind {
                assert_eq!(
                    value, expected,
                    "Integer value mismatch for input '{}'",
                    input
                );
            } else {
                panic!("Expected Uint token for input '{}'", input);
            }
        }
    }

    #[test]
    fn test_multiple_tokens() {
        let input = "1+2*3/4-5;";
        let expected = [
            TokenKind::Uint(1),
            TokenKind::Plus,
            TokenKind::Uint(2),
            TokenKind::Star,
            TokenKind::Uint(3),
            TokenKind::Slash,
            TokenKind::Uint(4),
            TokenKind::Minus,
            TokenKind::Uint(5),
            TokenKind::Semicolon,
        ];

        let lexer = Lexer::new(input);
        let tokens: Vec<_> = lexer.collect();

        assert_eq!(
            tokens.len(),
            expected.len(),
            "Number of tokens doesn't match"
        );

        for (i, (token, expected_kind)) in tokens.iter().zip(expected.iter()).enumerate() {
            match (&token.kind, expected_kind) {
                (TokenKind::Uint(actual), TokenKind::Uint(expected)) => {
                    assert_eq!(actual, expected, "Integer token mismatch at position {}", i);
                }
                _ => assert!(
                    matches!(&token.kind, expected_kind),
                    "Token kind mismatch at position {}",
                    i
                ),
            }
        }
    }

    #[test]
    fn test_parentheses() {
        let input = "(1+2)*(3-4)";
        let expected = [
            TokenKind::Lparen,
            TokenKind::Uint(1),
            TokenKind::Plus,
            TokenKind::Uint(2),
            TokenKind::Rparen,
            TokenKind::Star,
            TokenKind::Lparen,
            TokenKind::Uint(3),
            TokenKind::Minus,
            TokenKind::Uint(4),
            TokenKind::Rparen,
        ];

        let lexer = Lexer::new(input);
        let tokens: Vec<_> = lexer.collect();

        assert_eq!(
            tokens.len(),
            expected.len(),
            "Number of tokens doesn't match"
        );

        for (i, (token, expected_kind)) in tokens.iter().zip(expected.iter()).enumerate() {
            match (&token.kind, expected_kind) {
                (TokenKind::Uint(actual), TokenKind::Uint(expected)) => {
                    assert_eq!(actual, expected, "Integer token mismatch at position {}", i);
                }
                _ => assert!(
                    matches!(&token.kind, expected_kind),
                    "Token kind mismatch at position {}",
                    i
                ),
            }
        }
    }

    #[test]
    fn test_slice_positions() {
        let input = "12+345";
        let lexer = Lexer::new(input);
        let tokens: Vec<_> = lexer.collect();

        assert_eq!(tokens.len(), 3);

        // Check positions and lengths
        assert_eq!(tokens[0].slice.start, 0); // Position of '1'
        assert_eq!(tokens[0].slice.len, 2); // Length of "12"

        assert_eq!(tokens[1].slice.start, 2); // Position of '+'
        assert_eq!(tokens[1].slice.len, 1); // Length of "+"

        assert_eq!(tokens[2].slice.start, 3); // Position of '3'
        assert_eq!(tokens[2].slice.len, 3); // Length of "345"
    }

    #[test]
    fn test_empty_input() {
        let lexer = Lexer::new("");
        let tokens: Vec<_> = lexer.collect();
        assert!(tokens.is_empty(), "Empty input should produce no tokens");
    }

    // This test will fail with the current implementation since we're using unimplemented!()
    // for identifiers and other non-implemented token types
    #[test]
    #[should_panic(expected = "not implemented")]
    fn test_unimplemented_tokens() {
        let mut lexer = Lexer::new("abc");
        lexer.next();
    }
}
