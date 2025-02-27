use std::{error::Error, fmt::Display};

#[derive(Debug)]
pub enum LexerError {
    UnknownChar(char),
}

impl Display for LexerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownChar(ch) => write!(f, "LexerError: unknown character '{}'", ch),
        }
    }
}
impl Error for LexerError {}

pub type LexerResult<T> = Result<T, LexerError>;
