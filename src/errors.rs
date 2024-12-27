use std::{error::Error, fmt};
use crate::lexing::Token;
use crate::parsing::ParseNodeType;

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
    InsufficientTokens,
    UnexpectedParseNode(ParseNodeType, usize, usize),
}


impl Error for ParsingError {}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InsufficientTokens => write!(f, "Token stream ends unexpectedly!"),
            Self::InvalidToken(token, line, col) => 
                write!(f, "Invalid token '{:?}' on line {} at column {}", token.token_type, line, col),
            Self::UnexpectedParseNode(node_type, line, col) => 
                write!(f, "Unexpected parse node '{:?}' on line {} at column {}", node_type, line, col),
        }
    }
}


#[derive(Debug)]
pub enum SemanticError {
    InvalidType(String, usize, usize),
    UnknownSymbol(String, usize, usize),
}

impl Error for SemanticError {}

impl fmt::Display for SemanticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidType(type_name, line, col) => 
                write!(f, "Invalid type '{}' on line {} at column {}", type_name, line, col),
            Self::UnknownSymbol(symbol_name, line, col) => 
                write!(f, "Unknown symbol '{}' on line {} at column {}", symbol_name, line, col),
        }
    }
}
