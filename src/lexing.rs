use crate::errors::LexingError;

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Position {
    pub(crate) line: usize,
    pub(crate) col: usize,
    pub(crate) length: usize,
}


impl Position {
    #[allow(dead_code)]
    pub fn new(line: usize, col: usize, length: usize) -> Self {
        Self {
            line, col, length
        }
    }


    pub fn zeros() -> Self {
        Self {
            line: 0, col: 0, length: 0
        }
    }
}


#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub enum TokenType {
    Integer(u64),
    Float(f64),
    String(String),
    Identifier(String),
    FnKeyword,
    IfKeyword,
    ElseKeyword,
    OpenParen,
    CloseParen,
    OpenCurly,
    CloseCurly,
    OpenSquare,
    CloseSquare,
    Comma,
    Semicolon,
    Arrow,
    End,
    LetKeyword,
    ForKeyword,
    InKeyword,
    Equals,
    EqualsEquals,
    NotEquals,
    LessThan,
    GreaterThan,
    Plus,
    Minus,
    Star,
    Slash,
    Colon,
    DoubleColon
}


#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub(crate) token_type: TokenType,
    pub(crate) position: Position,
}


impl Token {
    pub fn new(token_type: TokenType, line: usize, col: usize, length: usize) -> Self {
        Self {
            token_type,
            position: Position { line, col, length },
        }
    }
}


pub struct Lexer {
    pub tokens: Vec<Token>,
    input: Vec<String>,
    line: usize,
    col: usize
}


impl Lexer {
    pub fn new(input: String) -> Self {
        Self {
            input: input.lines().map(|s| s.to_string()).collect(),
            tokens: Vec::new(),
            line: 1,
            col: 1,
        }
    }


    pub fn lex(&mut self) -> Result<(), LexingError> {
        let mut current_str: String = String::new();
        for line in self.input.clone() {
            for c in line.chars() {
                current_str.push(c);
                if let Some(token) = self.get_token(&current_str) {
                    self.tokens.push(token);
                    current_str.clear();
                }

                if current_str.starts_with(" ") {
                    current_str.remove(0);
                    self.col += 1;
                }
            }
            
            if !current_str.is_empty() {
                return Err(LexingError::UnterminatedString(self.line, self.col))
            }
            
            // move to the next line and reset the cols if there is another line to process,
            // otherwise add the end token and stop lexing
            if (self.line < self.input.len()) {
                self.col = 1;
                self.line += 1;
            } else {
                self.tokens.push(Token::new(TokenType::End, self.line, self.col, 0));
                break;
            }
        }

        Ok(())
    }


    fn get_token(&mut self, string: &str) -> Option<Token> {
        let token: Option<Token> = match string {
            "(" => Some(Token::new(TokenType::OpenParen, self.line, self.col, 1)),
            ")" => Some(Token::new(TokenType::CloseParen, self.line, self.col, 1)),
            "{" => Some(Token::new(TokenType::OpenCurly, self.line, self.col, 1)),
            "}" => Some(Token::new(TokenType::CloseCurly, self.line, self.col, 1)),
            "[" => Some(Token::new(TokenType::OpenSquare, self.line, self.col, 1)),
            "]" => Some(Token::new(TokenType::CloseSquare, self.line, self.col, 1)),
            ";" => Some(Token::new(TokenType::Semicolon, self.line, self.col, 1)),
            "," => Some(Token::new(TokenType::Comma, self.line, self.col, 1)),
            "+" => Some(Token::new(TokenType::Plus, self.line, self.col, 1)),
            ":" => {
                if self.assert_next_character_not(':', string.len() - 1) {
                    Some(Token::new(TokenType::Colon, self.line, self.col, 1))
                } else { None }
            }
            "=" => {
                if self.assert_next_character_not('=', string.len() - 1) {
                    Some(Token::new(TokenType::Equals, self.line, self.col, 1))
                } else { None }
            },
            "-" => {
                if self.assert_next_character_not('>', string.len() - 1) {
                    Some(Token::new(TokenType::Minus, self.line, self.col, 1))
                } else { None }
            },
            "::" => Some(Token::new(TokenType::DoubleColon, self.line, self.col, 2)),
            "*" => Some(Token::new(TokenType::Star, self.line, self.col, 1)),
            "/" => Some(Token::new(TokenType::Slash, self.line, self.col, 1)),
            "<" => Some(Token::new(TokenType::LessThan, self.line, self.col, 1)),
            ">" => Some(Token::new(TokenType::GreaterThan, self.line, self.col, 1)),
            "==" => Some(Token::new(TokenType::EqualsEquals, self.line, self.col, 2)),
            "!=" => Some(Token::new(TokenType::NotEquals, self.line, self.col, 2)),
            "->" => Some(Token::new(TokenType::Arrow, self.line, self.col, 2)),
            " " | "\n" | "\t" | "\r" => None,
            _ => {
                // check if this is the end of the line, return null if it is the end
                let next_char = self.input[self.line - 1]
                                          .chars().nth(self.col + string.len() - 1)
                                          .unwrap_or_else(|| '\0');
                
                // not the end of the token so keep going
                if next_char.is_alphanumeric() && !string.starts_with('"') {
                    None
                } else {
                    match string {
                        // reserved keywords
                        "fn" => Some(Token::new(TokenType::FnKeyword, self.line, self.col, 2)),
                        "let" => Some(Token::new(TokenType::LetKeyword, self.line, self.col, 3)),
                        "for" => Some(Token::new(TokenType::ForKeyword, self.line, self.col, 3)),
                        "in" => Some(Token::new(TokenType::InKeyword, self.line, self.col, 2)),
                        "if" => Some(Token::new(TokenType::IfKeyword, self.line, self.col, 2)),
                        "else" => Some(Token::new(TokenType::ElseKeyword, self.line, self.col, 4)),
                        
                        // a string or number literal
                        other => self.lex_literal(other, next_char)
                    }
                }
            }
        };

        if let Some(_) = token {
            self.col += string.len();
        }
        token
    }


    fn lex_literal(&mut self, string: &str, next_char: char) -> Option<Token> {
        // check for a valid identifier
        if regex::Regex::new(r"^[a-zA-Z_]([a-zA-Z_\d])*$").unwrap().is_match(string.trim()) {
            Some(Token::new(TokenType::Identifier(string.to_string()), self.line, self.col, string.len()))
        }
            
        // check for a valid integer
        else if regex::Regex::new(r"^(\d+)$").unwrap().is_match(string.trim()) && next_char != '.' {
            Some(Token::new(TokenType::Integer(string.parse::<u64>().unwrap()), self.line, self.col, string.len()))
        } 
        
        // check for a valid float
        else if regex::Regex::new(r"^(\d+\.\d+)$").unwrap().is_match(string.trim()) {
            Some(Token::new(TokenType::Float(string.parse::<f64>().unwrap()), self.line, self.col, string.len()))
        }
        
        // check for a valid string
        else if string.starts_with("\"") {
            if regex::Regex::new("\"(?:[^\"\\\\]|\\\\.)*\"").unwrap().is_match(string) {
                let string_value = string.trim_matches('"').to_string();
                Some(Token::new(TokenType::String(string_value), self.line, self.col, string.len()))
            } else {
                None
            }
        } 
        
        // token is either invalid or not yet completed
        else if next_char.is_whitespace() {
            panic!("Malformed token: {}", string);
        } else {
            None
        }
    }


    fn assert_next_character_not(&self, c: char, offset: usize) -> bool {
        let next_char = match self.input[self.line - 1].chars().nth(self.col + offset) {
            Some(c) => c,
            None => return true,
        };

        next_char != c
    }
}


#[cfg(test)]
mod tests {
    use crate::lexing;

    #[test]
    fn test_tokenize_simple_main() {
        let mut lexer = super::Lexer::new("fn main() -> int {}".to_string());
        lexer.lex().unwrap();
        assert_eq!(lexer.tokens.len(), 9);

        assert_eq!(lexer.tokens[0].token_type, super::TokenType::FnKeyword);

        assert_eq!(lexer.tokens[1].token_type, super::TokenType::Identifier("main".to_string()));
        assert_eq!(lexer.tokens[1].position.line, 1);
        assert_eq!(lexer.tokens[1].position.col, 4);

        assert_eq!(lexer.tokens.last().unwrap().token_type, super::TokenType::End);
        assert_eq!(lexer.tokens.last().unwrap().position.line, 1);
        assert_eq!(lexer.tokens.last().unwrap().position.col, 20);
    }

    #[test]
    fn test_tokenize_simple_main_extra_paren() {
        let mut lexer = super::Lexer::new("fn main()) -> int {}".to_string());
        lexer.lex().unwrap();
        assert_eq!(lexer.tokens.len(), 10);
    }

    #[test]
    #[should_panic]
    fn test_bad_token() {
        let mut lexer = super::Lexer::new("fn main() $ int {}()".to_string());
        lexer.lex().unwrap();
    }

    #[test]
    fn test_multiline_tokenization() {
        let mut lexer = super::Lexer::new("fn main() -> int {
            let x = 10;
            let y = 20;
            let z = x + y;
        }".to_string());
        lexer.lex().unwrap();
        assert_eq!(lexer.tokens.len(), 26);

        assert_eq!(lexer.tokens[1].token_type, super::TokenType::Identifier("main".to_string()));
        assert_eq!(lexer.tokens[1].position.line, 1);
        assert_eq!(lexer.tokens[1].position.col, 4);

        assert_eq!(lexer.tokens[12].token_type, super::TokenType::LetKeyword);
        assert_eq!(lexer.tokens[12].position.line, 3);
        assert_eq!(lexer.tokens[12].position.col, 13);

        assert_eq!(lexer.tokens[15].token_type, super::TokenType::Integer(20));
        assert_eq!(lexer.tokens[15].position.line, 3);
        assert_eq!(lexer.tokens[15].position.col, 21);
    }

    #[test]
    fn test_tokenize_all_tokens() {
        let mut lexer = super::Lexer::new("fn main() -> int {
            let x = 10;
            for y in z {
                if y == 0 { 1 } else { 0 }
        }".to_string());
        lexer.lex().unwrap();
        println!("{:#?}", lexer.tokens);
        assert_eq!(lexer.tokens.len(), 30);
    }


    #[test]
    #[should_panic]
    fn test_malformed_digraph() {
        let mut lexer = super::Lexer::new("fn main() -> int { =! }".to_string());
        lexer.lex().unwrap();
        println!("{:?}", lexer.tokens);
    }


    #[test]
    fn test_loop() {
        let mut lexer = lexing::Lexer::new("
            fn main() -> int {
                for z in [1,2,3] {
                    i
                }
            }
            ".to_string());
        lexer.lex().unwrap();
    }
    
    
    #[test]
    fn test_string_literal() {
        let mut lexer = lexing::Lexer::new("
            fn main() -> int {
                let x: str = \"hello world\";
            }
            ".to_string());
        lexer.lex().unwrap();
        assert_eq!(lexer.tokens.len(), 16);
        assert_eq!(lexer.tokens[12].token_type, lexing::TokenType::String("hello world".to_string()));
    }
    
    
    #[test]
    fn test_empty_string_literal() {
        let mut lexer = lexing::Lexer::new("
            fn main() -> int {
                let x: str = \"\";
            }
            ".to_string());
        lexer.lex().unwrap();

        assert_eq!(lexer.tokens[12].token_type, lexing::TokenType::String(String::new()));
    }
    
    
    #[test]
    #[should_panic]
    fn test_malformed_string_literal() {
        let mut lexer = lexing::Lexer::new("
            fn main() -> int {
                let x: str = \"hello world;
            }
            ".to_string());
        lexer.lex().unwrap();
    }
    
    
    #[test]
    fn test_float() {
        let mut lexer = lexing::Lexer::new("
            fn main() -> int {
                14.25
            }
            ".to_string());
        lexer.lex().unwrap();
        
        assert_eq!(lexer.tokens.len(), 10);
        assert_eq!(lexer.tokens[7].token_type, lexing::TokenType::Float(14.25));
    }
    
    
    #[test]
    #[should_panic]
    fn test_float_missing_prefix() {
        let mut lexer = lexing::Lexer::new("
            fn main() -> int {
                .25
            }
            ".to_string());
        lexer.lex().unwrap();
    }
    
    
    #[test]
    #[should_panic]
    fn test_float_missing_suffix() {
        let mut lexer = lexing::Lexer::new("
            fn main() -> int {
                14.
            }
            ".to_string());
        lexer.lex().unwrap();
    }
}
