use std::{error::Error, fmt};
use crate::lexing::Token;

#[allow(dead_code)]
#[derive(Debug)]
pub enum LexingError {
    UnrecognizedToken(String, usize, usize),
    UnterminatedString(usize, usize),
}


impl Error for LexingError {}

impl fmt::Display for LexingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnterminatedString(line, col) =>
                write!(f, "Unterminated string on line {} at column {}", line, col),
            Self::UnrecognizedToken(token, line, col) => 
                write!(f, "Unrecognized token '{}' on line {} at column {}", token, line, col),
        }
    }
}


#[derive(Debug)]
pub enum ParsingError {
    InvalidToken(Token, usize, usize),
    InsufficientTokens
}


impl Error for ParsingError {}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InsufficientTokens => write!(f, "Token stream ends unexpectedly!"),
            Self::InvalidToken(token, line, col) => 
                write!(f, "Invalid token '{:?}' on line {} at column {}", token.token_type, line, col),
        }
    }
}
