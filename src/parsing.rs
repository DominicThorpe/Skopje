use crate::errors::ParsingError;
use crate::errors::ParsingError::InsufficientTokens;
use crate::lexing::{Position, Token, TokenType};

#[allow(dead_code)]
#[derive(Debug)]
pub enum ParseNodeType {
    /// List of function declarations,
    Program(Vec<ParseNode>),
    /// Function name, parameters list, body, return type
    FunctionDeclaration(String, Vec<ParseNode>, Box<ParseNode>, Box<ParseNode>),
    /// Parameter name, parameter type
    FunctionParameter(String, Box<ParseNode>),
    /// Plain identifier
    Identifier(String),
    /// An integer literal
    IntegerLiteral(u64),
    /// Unit type
    Unit
}


#[derive(Debug)]
pub struct ParseNode {
    node_type: ParseNodeType,
    position: Position
}


impl ParseNode {
    fn new(node_type: ParseNodeType, position: Position) -> Self {
        Self {
            node_type,
            position
        }
    }
}


pub struct Parser {
    tokenstream: Vec<Token>,
}


impl Parser {
    pub fn new(tokenstream: Vec<Token>) -> Self {
        Self {
            tokenstream,
        }
    }


    /// Asserts that the next token in the token stream matches the expected token type.
    ///
    /// If the next token in the stream does not match the specified `token_type`, this function 
    /// will return an error of type `ParsingError`.
    /// If the token matches the expected type, it is removed from the token stream.
    ///
    /// # Arguments
    ///
    /// * `token_type` - The expected type of the next token in the token stream.
    ///
    /// # Returns
    ///
    /// - `Ok(())` if the next token matches the expected type and is successfully removed from the 
    /// stream.
    /// - `Err(ParsingError)` if:
    ///   - The token stream is empty, indicating no token to validate.
    ///   - The next token does not match the expected `token_type`.
    ///
    /// # Errors
    ///
    /// Returns a `ParsingError::InvalidToken` error in the following cases:
    /// - If the token stream is empty, indicating an invalid or unexpected token 
    ///   is encountered. In this case, the position of the error is set to `(0, 0)`.
    /// - If the next token in the stream does not match the provided `token_type`, 
    ///   the error will include the mismatched token and its position (line and column).
    ///
    /// # Example
    ///
    /// ```rust
    /// use crate::lexing::{TokenType, Token, Position};
    /// use crate::errors::ParsingError;
    /// use crate::parser::Parser;
    ///
    /// let tokens = vec![Token {
    ///     token_type: TokenType::OpenParen,
    ///     position: Position { line: 1, col: 1, length: 1 },
    /// }];
    /// let mut parser = Parser::new(tokens);
    ///
    /// // This will succeed since the first token type is `OpenParen`.
    /// assert!(parser.assert_next_token_of_type(TokenType::OpenParen).is_ok());
    ///
    /// // This will fail since the token stream is now empty, returning an error.
    /// assert!(parser.assert_next_token_of_type(TokenType::CloseParen).is_err());
    /// ```
    fn assert_next_token_of_type(&mut self, token_type: TokenType) -> Result<(), ParsingError> {
        // Error handling in case the token stream ends prematurely
        let first_token = match self.tokenstream.first() {
            Some(token) => token,
            None => return Err(ParsingError::InsufficientTokens)
        };
        
        // check that the token type of the next token is the same as the expected token type
        if first_token.token_type != token_type {
            return Err(ParsingError::InvalidToken(
                first_token.clone(), 
                first_token.position.line, 
                first_token.position.col
            ));
        }

        self.tokenstream.remove(0);
        Ok(())
    }


    /// Parses the token stream and constructs the root parse node representing a program.
    ///
    /// This method initiates the parsing process by creating the root node of type
    /// `Program`. It assumes that the token stream contains at least one valid
    /// function declaration, which it delegates to the `parse_function_declaration`
    /// method for detailed parsing.
    ///
    /// # Returns
    ///
    /// - `Ok(ParseNode)` containing the root node of the parse tree with the program's structure
    ///   if parsing succeeds.
    /// - `Err(ParsingError)` if any parsing error occurs during the function declaration parsing
    ///   (as delegated by `parse_function_declaration`).
    ///
    /// # Errors
    ///
    /// This method will return a `ParsingError` propagated from the `parse_function_declaration`
    /// method in case a function declaration in the token stream is invalid or malformed.
    ///
    /// # Structure of Returned Node
    ///
    /// The returned `ParseNode` will:
    /// - Have a `node_type` of `ParseNodeType::Program`.
    /// - Contain a `Vec` of child nodes, each representing a parsed function declaration.
    /// - Have its position set to `(1, 1)` (line 1, column 1) as it represents the root of
    ///   the entire program.
    ///
    /// # Example
    ///
    /// ```rust
    /// use crate::lexing::{TokenType, Token, Position};
    /// use crate::errors::ParsingError;
    /// use crate::parser::{ParseNode, ParseNodeType, Parser};
    ///
    /// let tokens = vec![/* token stream for a valid program */];
    /// let mut parser = Parser::new(tokens);
    ///
    /// match parser.parse() {
    ///     Ok(node) => {
    ///         // Successfully parsed the program.
    ///         assert!(matches!(node.node_type, ParseNodeType::Program(_)));
    ///     }
    ///     Err(error) => {
    ///         // Handle the parsing error.
    ///         eprintln!("Parsing failed with error: {:?}", error);
    ///     }
    /// }
    /// ```
    pub fn parse(&mut self) -> Result<ParseNode, ParsingError> {
        Ok(
            ParseNode::new(
                ParseNodeType::Program(vec![self.parse_function_declaration()?]), 
               Position { line: 1, col: 1, length: 0 }
            ))
    }


    /// Parses a function declaration from the token stream.
    ///
    /// The function declaration is expected to consist of a function keyword, an
    /// identifier for the function name, a list of parameters within parentheses,
    /// return type after an arrow, and a curly-braces-enclosed body.
    ///
    /// # Returns
    ///
    /// - `Ok(ParseNode)` if a valid function declaration is found and successfully parsed.
    /// - `Err(ParsingError)` in case of parsing issues, like invalid token types or syntax errors.
    fn parse_function_declaration(&mut self) -> Result<ParseNode, ParsingError> {
        self.assert_next_token_of_type(TokenType::FnKeyword)?;
        
        // get the name of the function
        let next_token = self.get_next_token_required()?;
        let declaration_pos = next_token.position;
        let identifier = match next_token.token_type.clone() {
            TokenType::Identifier(identifier) => identifier,
            _ => return Err(ParsingError::InvalidToken(
                next_token.clone(), 
                declaration_pos.line, 
                declaration_pos.col
            )),
        };
        
        // get the parameters of the function
        self.assert_next_token_of_type(TokenType::OpenParen)?;
        let params = self.parse_function_params()?;
        self.assert_next_token_of_type(TokenType::Arrow)?;
        
        // get the return type of the function
        let next_token = self.get_next_token_required()?;
        let return_type = match next_token.token_type.clone() {
            TokenType::Identifier(identifier) => 
                ParseNode::new(ParseNodeType::Identifier(identifier), next_token.position),
            _ => return Err(ParsingError::InvalidToken(next_token.clone(), 0, 0)),
        };
        self.tokenstream.remove(0);
        
        // get the return type of the function
        self.assert_next_token_of_type(TokenType::OpenCurly)?;
        let body = self.parse_expression()?;
        self.assert_next_token_of_type(TokenType::CloseCurly)?;
        
        let node_type = ParseNodeType::FunctionDeclaration(
            identifier.to_string(), 
            params, 
            Box::new(body), 
            Box::new(return_type)
        );
        
        Ok(ParseNode::new(node_type, declaration_pos))
    }


    /// Parses function parameters from the token stream.
    ///
    /// It processes a list of comma-separated function parameters enclosed within parentheses.
    /// Each parameter is expected to be an identifier followed by a colon and its type.
    ///
    /// # Returns
    ///
    /// - `Ok(Vec<ParseNode>)` if the parameters are successfully parsed, with each element in the Vector 
    ///   representing a single parameter (identifier and type).
    /// - `Err(ParsingError)` in case of invalid or unexpected tokens in the list of parameters.
    fn parse_function_params(&mut self) -> Result<Vec<ParseNode>, ParsingError> {
        let mut params: Vec<ParseNode> = Vec::new();
        loop {
            match self.tokenstream.first().unwrap().token_type.clone() {
                // end of the parameters list
                TokenType::CloseParen => { self.tokenstream.remove(0); break },
                // there are more parameters to come
                TokenType::Comma => { self.tokenstream.remove(0); continue },
                // start of a new parameter of the form <IDENTIFIER> : <TYPE>
                TokenType::Identifier(identifier) => {
                    self.tokenstream.remove(0);
                    
                    self.assert_next_token_of_type(TokenType::Colon)?;
                    
                    // get the type of the parameter
                    let param_type = match &self.tokenstream.first().unwrap().token_type {
                        TokenType::Identifier(s) => 
                            ParseNode::new(ParseNodeType::Identifier(s.to_string()), Position::zeros()),
                        _ => return Err(ParsingError::InvalidToken(self.tokenstream.first().unwrap().clone(), 0, 0)),
                    };
                    self.tokenstream.remove(0);
                    
                    let node_type = ParseNodeType::FunctionParameter(
                        identifier.to_string(), 
                        Box::new(param_type)
                    );
                    params.push(ParseNode::new(node_type, Position::zeros()));
                },
                _ => return Err(ParsingError::InvalidToken(self.tokenstream.first().unwrap().clone(), 0, 0)),
            }
        }

        Ok(params)
    }
    
    
    fn parse_expression(&mut self) -> Result<ParseNode, ParsingError> {
        self.parse_value()
    }
    
    
    fn parse_value(&mut self) -> Result<ParseNode, ParsingError> {
         let node_type = match &self.tokenstream.first().unwrap().token_type {
             TokenType::Identifier(s) => ParseNodeType::Identifier(s.clone()),
             TokenType::Integer(i) => ParseNodeType::IntegerLiteral(*i),
             TokenType::String(s) => todo!(),
             _ => return Err(ParsingError::InvalidToken(self.tokenstream.first().unwrap().clone(), 0, 0)),
         };
        self.tokenstream.remove(0);
        
        Ok(ParseNode::new(node_type, Position::zeros()))
    }
    
    
    fn get_next_token_required(&mut self) -> Result<&Token, ParsingError> {
        match self.tokenstream.first() {
            Some(token) => Ok(token),
            None => Err(ParsingError::InsufficientTokens)
        }
    }
}
