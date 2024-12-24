use std::{error::Error, fmt};

#[derive(Debug)]
pub enum LexingError {
    UnrecognizedToken(String, usize, usize),
}


impl Error for LexingError {}


impl fmt::Display for LexingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnrecognizedToken(token, line, col) => 
                write!(f, "Unrecognized token '{}' on line {} at column {}", token, line, col),
        }
    }
}
