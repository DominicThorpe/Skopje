use crate::errors::ParsingError;
use crate::lexing::{Position, Token, TokenType};
use crate::lexing::TokenType::LetKeyword;
use crate::parsing::ParseNodeType::IfElseStatement;

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub enum ParseNodeType {
    /// List of function declarations,
    Program(Vec<ParseNode>),
    /// Function name, parameters list, body, return type
    FunctionDeclaration(String, Vec<ParseNode>, Box<ParseNode>, Box<ParseNode>),
    /// Parameter name, parameter type
    FunctionParameter(String, Box<ParseNode>),
    /// If statement condition, if true body, if false body 
    IfElseStatement(Box<ParseNode>, Box<ParseNode>, Box<ParseNode>),
    /// For loop iterator variable, iterator variable type, array to iterate over, and body of 
    /// iterator
    Loop(Box<ParseNode>, Box<ParseNode>, Box<ParseNode>, Box<ParseNode>),
    /// Identifier to assign, variable type, expression to assign, continuation
    Assignment(String, Box<ParseNode>, Box<ParseNode>, Box<ParseNode>),
    /// Plain identifier
    Identifier(String),
    /// An integer literal
    IntegerLiteral(u64),
    /// A float literal
    FloatLiteral(f64),
    /// A string literal
    StringLiteral(String),
    /// Elements of the array literal
    ArrayLiteral(Vec<ParseNode>),
    /// Operation, left expression, right expression
    BinaryOperation(String, Box<ParseNode>, Box<ParseNode>),
    /// Operation, sub-expression
    UnaryOperation(String, Box<ParseNode>),
    /// Array being indexes, and expression of index
    ArrayIndexOperation(Box<ParseNode>, Box<ParseNode>),
    /// Function name, vector of parameter expressions
    FunctionCall(String, Vec<ParseNode>),
    /// Type contained within the array, which may be another array type
    ArrayType(Box<ParseNode>),
    /// Unit type
    Unit
}


#[derive(Debug, Clone, PartialEq)]
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
        self.tokenstream.remove(0);

        // get the parameters of the function
        self.assert_next_token_of_type(TokenType::OpenParen)?;
        let params = self.parse_function_params()?;
        self.assert_next_token_of_type(TokenType::Arrow)?;

        // get the return type of the function
        let return_type = self.parse_type()?;

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
    
    
    fn parse_type(&mut self) -> Result<ParseNode, ParsingError> {
        let next_token = self.get_next_token_required()?.clone();
        let token_pos = next_token.position;
        self.tokenstream.remove(0);
        
        match next_token.token_type {
            TokenType::OpenSquare => {
                let result = ParseNode::new(
                    ParseNodeType::ArrayType(Box::new(self.parse_type()?)), 
                    token_pos
                );
                self.assert_next_token_of_type(TokenType::CloseSquare)?;
                Ok(result)
            }
            TokenType::Identifier(identifier) => Ok(ParseNode::new(
                ParseNodeType::Identifier(identifier.to_string()), 
                token_pos
            )),
            _ => Err(ParsingError::InvalidToken(next_token.clone(), token_pos.line, token_pos.col))
        }
    }


    /// Parses function parameters from the token stream.
    ///
    /// It processes a list of comma-separated function parameters enclosed within parentheses.
    /// Each parameter is expected to be an identifier followed by a colon and its type.
    ///
    /// # Returns
    ///
    /// - `Ok(Vec<ParseNode>)` if the parameters are successfully parsed, with each element in the 
    ///   Vector representing a single parameter (identifier and type).
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
                    let param_type = self.parse_type()?;
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
    
    
    fn pratt_parse_expr(&mut self, min_power: u8) -> Result<ParseNode, ParsingError> { 
        let mut lhs = match self.get_next_token_required()?.token_type {
            TokenType::Minus => {
                self.tokenstream.remove(0);
                let (_, right_power) = self.get_prefix_binding_power("-");
                let rhs = self.pratt_parse_expr(right_power)?;
                ParseNode::new(ParseNodeType::UnaryOperation("-".to_string(), Box::new(rhs)), Position::zeros())
            }
            TokenType::Plus => {
                self.tokenstream.remove(0);
                let (_, right_power) = self.get_prefix_binding_power("+");
                let rhs = self.pratt_parse_expr(right_power)?;
                ParseNode::new(ParseNodeType::UnaryOperation("-".to_string(), Box::new(rhs)), Position::zeros())
            }
            TokenType::OpenParen => {
                self.tokenstream.remove(0);
                let lhs = self.pratt_parse_expr(0)?;
                self.assert_next_token_of_type(TokenType::CloseParen)?;
                lhs
            }
            _ => self.parse_value()?
        };
        
        loop {
            let next_token = match self.get_next_token_required() {
                Ok(t) => t,
                Err(_) => break
            };
            
            let op = match &next_token.token_type {
                TokenType::Plus => "+",
                TokenType::Minus => "-",
                TokenType::Star => "*",
                TokenType::Slash => "/",
                TokenType::DoubleColon => "::",
                TokenType::OpenSquare => "[",
                _ => break
            };
            
            if let Some((left_power, ())) = self.get_postfix_binding_power(op) {
                if left_power < min_power {
                    break;
                }
                self.tokenstream.remove(0);
                
                lhs = if op == "[" {
                    let rhs = self.pratt_parse_expr(0)?;
                    self.assert_next_token_of_type(TokenType::CloseSquare)?;
                    ParseNode::new(ParseNodeType::ArrayIndexOperation(
                        Box::new(lhs),
                        Box::new(rhs)
                    ), Position::zeros())
                } else {
                    ParseNode::new(ParseNodeType::UnaryOperation(
                        op.to_string(),
                        Box::new(lhs)),
                        Position::zeros()
                    )
                };
                continue;
            }
                        
            let (left_power, right_power) = self.get_infix_binding_power(op);
            if left_power < min_power {
                break;
            }
            
            let _ = self.get_next_token_required()?;
            self.tokenstream.remove(0);
            
            let rhs = self.pratt_parse_expr(right_power)?;
            lhs = ParseNode::new(ParseNodeType::BinaryOperation(
                op.to_string(), 
                Box::new(lhs), 
                Box::new(rhs)
            ), Position::zeros());
        }
        
        Ok(lhs)
    }
    
    
    fn get_postfix_binding_power(&self, op: &str) -> Option<(u8, ())> {
        match op {
            "++" | "--" | "[" => Some((9, ())),
            _ => None
        }
    }
    
    
    fn get_infix_binding_power(&self, op: &str) -> (u8, u8) {
        match op {
            "+" | "-" => (1, 2),
            "*" | "/" => (3, 4),
            "::" => (5, 6),
            _ => panic!("Invalid operator")
        }
    }
    
    
    fn get_prefix_binding_power(&self, op: &str) -> ((), u8) {
        match op {
            "+" | "-" => ((), 8),
            _ => panic!("Invalid operator")
        }
    }


    fn parse_expression(&mut self) -> Result<ParseNode, ParsingError> {
        let next_token = self.get_next_token_required()?.clone();
        match next_token.token_type {
            TokenType::IfKeyword => self.parse_selection(next_token.position),
            TokenType::ForKeyword => self.parse_loop(next_token.position),
            TokenType::LetKeyword => self.parse_assignment(next_token.position),
            _ => self.pratt_parse_expr(0)
        }
    }
    
    
    fn parse_selection(&mut self, position: Position) -> Result<ParseNode, ParsingError> {
        self.tokenstream.remove(0);
        
        let condition = self.parse_expression()?;
        self.assert_next_token_of_type(TokenType::OpenCurly)?;
        let true_branch = self.parse_expression()?;
        self.assert_next_token_of_type(TokenType::CloseCurly)?;
        self.assert_next_token_of_type(TokenType::ElseKeyword)?;
        self.assert_next_token_of_type(TokenType::OpenCurly)?;
        let false_branch = self.parse_expression()?;
        self.assert_next_token_of_type(TokenType::CloseCurly)?;
        
        let node_type = IfElseStatement(
            Box::new(condition), 
            Box::new(true_branch), 
            Box::new(false_branch)
        );
        Ok(ParseNode::new(node_type, position))
    }
    
    
    fn parse_loop(&mut self, position: Position) -> Result<ParseNode, ParsingError> {
        self.tokenstream.remove(0); // remove the "for" token
        
        // get the iteration variable identifier
        let next_token = self.get_next_token_required()?;
        let next_token_pos = next_token.position;
        let id_token_type = match &next_token.token_type {
            TokenType::Identifier(id) => ParseNodeType::Identifier(id.to_string()),
            _ => return Err(ParsingError::InvalidToken(
                next_token.clone(), 
                next_token_pos.col, 
                next_token_pos.line
            ))
        };
        let id_token = ParseNode::new(id_token_type, next_token_pos);
        self.tokenstream.remove(0);
        
        // get the iteration variable type
        self.assert_next_token_of_type(TokenType::Colon)?;
        let next_token = self.get_next_token_required()?;
        let next_token_pos = next_token.position;
        let iter_type_token_type = match &next_token.token_type {
            TokenType::Identifier(id) => ParseNodeType::Identifier(id.to_string()),
            _ => return Err(ParsingError::InvalidToken(
                next_token.clone(),
                next_token_pos.col,
                next_token_pos.line
            ))
        };
        let type_token = ParseNode::new(iter_type_token_type, next_token_pos);
        self.tokenstream.remove(0);
        
        // get the array to iterate over
        self.assert_next_token_of_type(TokenType::InKeyword)?;
        let iter_array = self.parse_expression()?;
        
        // get the expression in the body
        self.assert_next_token_of_type(TokenType::OpenCurly)?;
        let body = self.parse_expression()?;
        self.assert_next_token_of_type(TokenType::CloseCurly)?;
        
        Ok(ParseNode::new(ParseNodeType::Loop(
            Box::new(id_token),
            Box::new(type_token),
            Box::new(iter_array),
            Box::new(body)
        ), position.clone()))
    }
    
    
    fn parse_assignment(&mut self, position: Position) -> Result<ParseNode, ParsingError> {
        self.assert_next_token_of_type(LetKeyword)?;
        
        // get identifier
        let next_token = self.get_next_token_required()?.clone();
        self.tokenstream.remove(0);
        let token_pos = next_token.position;
        let identifier = match &next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(ParsingError::InvalidToken(
                next_token.clone(), 
                token_pos.line, 
                token_pos.col
            ))
        };
        
        // get type
        self.assert_next_token_of_type(TokenType::Colon)?;
        let type_node = self.parse_type()?;
        
        self.assert_next_token_of_type(TokenType::Equals)?;
        let expression = self.parse_expression()?;        
        self.assert_next_token_of_type(TokenType::Semicolon)?;
        
        // parse continuation
        let continuation = self.parse_expression()?;
        
        Ok(ParseNode::new(ParseNodeType::Assignment(
            identifier.to_string(),
            Box::new(type_node),
            Box::new(expression),
            Box::new(continuation)
        ), position.clone()))
    }


    fn parse_value(&mut self) -> Result<ParseNode, ParsingError> {
        let next_token = self.get_next_token_required()?.clone();
        let node_type = match &next_token.token_type {
            TokenType::Identifier(s) => 
                return self.parse_identifier_or_function_call(s, next_token.position),
            TokenType::Integer(i) => ParseNodeType::IntegerLiteral(*i),
            TokenType::OpenSquare => return self.parse_array_literal(),
            TokenType::String(s) => ParseNodeType::StringLiteral(s.clone()),
            TokenType::Float(f) => ParseNodeType::FloatLiteral(*f),
            _ => return Err(ParsingError::InvalidToken(self.tokenstream.first().unwrap().clone(), 0, 0)),
        };
        self.tokenstream.remove(0);

        Ok(ParseNode::new(node_type, Position::zeros()))
    }
    
    
    fn parse_identifier_or_function_call(&mut self, id: &str, pos: Position) -> Result<ParseNode, ParsingError> {
        self.tokenstream.remove(0);
        
        let next_token = self.get_next_token_required()?; 
        match next_token.token_type {
            TokenType::OpenParen => {
                let arguments = self.parse_function_call_params()?;
                Ok(ParseNode::new(ParseNodeType::FunctionCall(id.to_string(), arguments), pos))
            },
            _ => Ok(ParseNode::new(ParseNodeType::Identifier(id.to_string()), pos))
        }
    }
    
    
    fn parse_function_call_params(&mut self) -> Result<Vec<ParseNode>, ParsingError> {
        self.tokenstream.remove(0);
        let mut params: Vec<ParseNode> = vec![];
        
        loop {
            let next_token = self.get_next_token_required()?;
            match next_token.token_type {
                TokenType::CloseParen => { self.tokenstream.remove(0); break },
                TokenType::Comma => { self.tokenstream.remove(0); continue },
                _ => {
                    params.push(self.parse_expression()?);
                } 
            }
        }
        
        Ok(params)
    }
    
    
    fn parse_array_literal(&mut self) -> Result<ParseNode, ParsingError> {
        self.assert_next_token_of_type(TokenType::OpenSquare)?;
        
        let mut elems = vec![];
        loop {
            let next_token = self.get_next_token_required()?.clone();
            match next_token.token_type {
                TokenType::CloseSquare => { self.tokenstream.remove(0); break },
                TokenType::Comma => { self.tokenstream.remove(0); continue },
                _ => {
                    elems.push(self.parse_expression()?);
                }
            }
        }
        
        Ok(ParseNode::new(ParseNodeType::ArrayLiteral(elems), Position::zeros()))
    }


    fn get_next_token_required(&mut self) -> Result<&Token, ParsingError> {
        match self.tokenstream.first() {
            Some(token) => Ok(token),
            None => Err(ParsingError::InsufficientTokens)
        }
    }
}


#[cfg(test)]
mod tests {
    use crate::lexing::Token;
    use super::{ParseNodeType, Position, TokenType};
    use super::{Parser}; // Replace with the actual parser struct name.

    #[test]
    fn test_empty_array() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::OpenSquare, 0, 0, 0), // [
            Token::new(TokenType::CloseSquare, 0, 0, 0), // ]
        ]);

        let result = parser.parse_array_literal();
        assert!(result.is_ok());
        let node = result.unwrap();

        // Assert that the parsed node is an empty array
        assert_eq!(node.node_type, ParseNodeType::ArrayLiteral(vec![]));
    }

    #[test]
    fn test_single_element_array() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::OpenSquare, 0, 0, 0),  // [
            Token::new(TokenType::Integer(1), 0, 0, 0),  // 1
            Token::new(TokenType::CloseSquare, 0, 0, 0), // ]
        ]);

        let result = parser.parse_array_literal();
        assert!(result.is_ok());
        let node = result.unwrap();

        // Assert that the parsed node contains one element
        match node.node_type {
            ParseNodeType::ArrayLiteral(elems) => {
                assert_eq!(elems.len(), 1);
                assert_eq!(elems[0].node_type, (ParseNodeType::IntegerLiteral(1)));
            }
            _ => panic!("Expected an ArrayLiteral"),
        }
    }

    #[test]
    fn test_multiple_element_array() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::OpenSquare, 0, 0, 0),  // [
            Token::new(TokenType::Integer(1), 0, 0, 0),  // 1
            Token::new(TokenType::Comma, 0, 0, 0),       // ,
            Token::new(TokenType::Integer(2), 0, 0, 0),  // 2
            Token::new(TokenType::Comma, 0, 0, 0),       // ,
            Token::new(TokenType::Integer(3), 0, 0, 0),  // 3
            Token::new(TokenType::CloseSquare, 0, 0, 0), // ]
        ]);

        let result = parser.parse_array_literal();
        assert!(result.is_ok());
        let node = result.unwrap();

        // Assert that the parsed node contains multiple elements
        match node.node_type {
            ParseNodeType::ArrayLiteral(elems) => {
                assert_eq!(elems.len(), 3);
                assert_eq!(elems[0].node_type, ParseNodeType::IntegerLiteral(1));
                assert_eq!(elems[1].node_type, ParseNodeType::IntegerLiteral(2));
                assert_eq!(elems[2].node_type, ParseNodeType::IntegerLiteral(3));
            }
            _ => panic!("Expected an ArrayLiteral"),
        }
    }

    #[test]
    fn test_array_with_trailing_comma() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::OpenSquare, 0, 0, 0),  // [
            Token::new(TokenType::Integer(1), 0, 0, 0),  // 1
            Token::new(TokenType::Comma, 0, 0, 0),       // ,
            Token::new(TokenType::Integer(2), 0, 0, 0),  // 2
            Token::new(TokenType::Comma, 0, 0, 0),       // ,
            Token::new(TokenType::CloseSquare, 0, 0, 0), // ]
        ]);

        let result = parser.parse_array_literal();
        assert!(result.is_ok());
        let node = result.unwrap();

        match node.node_type {
            ParseNodeType::ArrayLiteral(elems) => {
                assert_eq!(elems.len(), 2);
                assert_eq!(elems[0].node_type, ParseNodeType::IntegerLiteral(1));
                assert_eq!(elems[1].node_type, ParseNodeType::IntegerLiteral(2));
            }
            _ => panic!("Expected an ArrayLiteral"),
        }
    }

    #[test]
    fn test_nested_arrays() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::OpenSquare, 0, 0, 0),   // [
            Token::new(TokenType::OpenSquare, 0, 0, 0),   // [
            Token::new(TokenType::Integer(1), 0, 0, 0),   // 1
            Token::new(TokenType::Comma, 0, 0, 0),        // ,
            Token::new(TokenType::Integer(2), 0, 0, 0),   // 2
            Token::new(TokenType::CloseSquare, 0, 0, 0),  // ]
            Token::new(TokenType::Comma, 0, 0, 0),        // ,
            Token::new(TokenType::OpenSquare, 0, 0, 0),   // [
            Token::new(TokenType::Integer(3), 0, 0, 0),   // 3
            Token::new(TokenType::Comma, 0, 0, 0),        // ,
            Token::new(TokenType::Integer(4), 0, 0, 0),   // 4
            Token::new(TokenType::CloseSquare, 0, 0, 0),  // ]
            Token::new(TokenType::CloseSquare, 0, 0, 0),  // ]
        ]);

        let result = parser.parse_array_literal();
        assert!(result.is_ok());
        let node = result.unwrap();

        match node.node_type {
            ParseNodeType::ArrayLiteral(elems) => {
                assert_eq!(elems.len(), 2);

                // First nested array
                match &elems[0].node_type {
                    ParseNodeType::ArrayLiteral(inner_elems) => {
                        assert_eq!(inner_elems.len(), 2);
                        assert_eq!(inner_elems[0].node_type, ParseNodeType::IntegerLiteral(1));
                        assert_eq!(inner_elems[1].node_type, ParseNodeType::IntegerLiteral(2));
                    }
                    _ => panic!("Expected a nested ArrayLiteral"),
                }

                // Second nested array
                match &elems[1].node_type {
                    ParseNodeType::ArrayLiteral(inner_elems) => {
                        assert_eq!(inner_elems.len(), 2);
                        assert_eq!(inner_elems[0].node_type, ParseNodeType::IntegerLiteral(3));
                        assert_eq!(inner_elems[1].node_type, ParseNodeType::IntegerLiteral(4));
                    }
                    _ => panic!("Expected a nested ArrayLiteral"),
                }
            }
            _ => panic!("Expected an ArrayLiteral"),
        }
    }

    #[test]
    #[should_panic]
    fn test_missing_closing_square_bracket() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::OpenSquare, 0, 0, 0),  // [
            Token::new(TokenType::Integer(1), 0, 0, 0),  // 1
            Token::new(TokenType::Comma, 0, 0, 0),       // ,
            Token::new(TokenType::Integer(2), 0, 0, 0),  // 2
            // Missing TokenType::CloseSquare
        ]);

        let _ = parser.parse_array_literal().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_invalid_token_in_array() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::OpenSquare, 0, 0, 0),  // [
            Token::new(TokenType::Integer(1), 0, 0, 0),  // 1
            Token::new(TokenType::Comma, 0, 0, 0),       // ,
            Token::new(TokenType::ForKeyword, 0, 0, 0),     // Invalid token
            Token::new(TokenType::CloseSquare, 0, 0, 0), // ]
        ]);

        parser.parse_array_literal().unwrap();
    }

    #[test]
    fn test_valid_assignment() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::LetKeyword, 1, 1, 3),   // let
            Token::new(TokenType::Identifier(String::from("x")), 1, 5, 1), // x
            Token::new(TokenType::Colon, 1, 6, 1),        // :
            Token::new(TokenType::Identifier(String::from("int")), 1, 8, 3), // int
            Token::new(TokenType::Equals, 1, 12, 1),      // =
            Token::new(TokenType::Integer(42), 1, 14, 2), // 42
            Token::new(TokenType::Semicolon, 1, 16, 1),   // ;
            Token::new(TokenType::Integer(1), 1, 18, 1), // x (continuation)
        ]);

        let node = parser.parse_assignment(Position::new(1, 1, 3)).unwrap();
        match node.node_type {
            ParseNodeType::Assignment(identifier, type_node, expression, continuation) => {
                assert_eq!(identifier, "x");

                // Check the type node
                match type_node.node_type {
                    ParseNodeType::Identifier(type_name) => assert_eq!(type_name, "int"),
                    _ => panic!("Expected Identifier for type node"),
                }

                // Check the expression
                match expression.node_type {
                    ParseNodeType::IntegerLiteral(value) => assert_eq!(value, 42),
                    _ => panic!("Expected IntegerLiteral for expression"),
                }

                // Check the continuation
                match continuation.node_type {
                    ParseNodeType::IntegerLiteral(val) => assert_eq!(val, 1),
                    _ => panic!("Expected Identifier for continuation"),
                }
            }
            _ => panic!("Expected an Assignment node"),
        }
    }

    #[test]
    #[should_panic]
    fn test_assignment_without_continuation() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::LetKeyword, 1, 1, 3),   // let
            Token::new(TokenType::Identifier(String::from("x")), 1, 5, 1), // x
            Token::new(TokenType::Colon, 1, 6, 1),        // :
            Token::new(TokenType::Identifier(String::from("float")), 1, 8, 5), // float
            Token::new(TokenType::Equals, 1, 14, 1),      // =
            Token::new(TokenType::Integer(99), 1, 16, 2), // 99
            Token::new(TokenType::Semicolon, 1, 18, 1),   // ;
        ]);

        parser.parse_assignment(Position::new(1, 1, 3)).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_assignment_with_invalid_type() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::LetKeyword, 1, 1, 3),   // let
            Token::new(TokenType::Identifier(String::from("x")), 1, 5, 1), // x
            Token::new(TokenType::Colon, 1, 6, 1),        // :
            Token::new(TokenType::ForKeyword, 1, 8, 3),   // Invalid type (for)
            Token::new(TokenType::Equals, 1, 12, 1),      // =
            Token::new(TokenType::Integer(42), 1, 14, 2), // 42
            Token::new(TokenType::Semicolon, 1, 16, 1),   // ;
        ]);

        parser.parse_assignment(Position::new(1, 1, 3)).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_assignment_with_missing_equals() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::LetKeyword, 1, 1, 3),   // let
            Token::new(TokenType::Identifier(String::from("x")), 1, 5, 1), // x
            Token::new(TokenType::Colon, 1, 6, 1),        // :
            Token::new(TokenType::Identifier(String::from("int")), 1, 8, 3), // int
            // Missing equals
            Token::new(TokenType::Integer(42), 1, 14, 2), // 42
            Token::new(TokenType::Semicolon, 1, 16, 1),   // ;
        ]);

        parser.parse_assignment(Position::new(1, 1, 3)).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_assignment_with_missing_semicolon() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::LetKeyword, 1, 1, 3),   // let
            Token::new(TokenType::Identifier(String::from("x")), 1, 5, 1), // x
            Token::new(TokenType::Colon, 1, 6, 1),        // :
            Token::new(TokenType::Identifier(String::from("int")), 1, 8, 3), // int
            Token::new(TokenType::Equals, 1, 12, 1),      // =
            Token::new(TokenType::Integer(42), 1, 14, 2), // 42
            // Missing semicolon
        ]);

        parser.parse_assignment(Position::new(1, 1, 3)).unwrap();
    }

    #[test]
    fn test_valid_if_else() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::IfKeyword, 1, 1, 2),          // if
            Token::new(TokenType::Identifier(String::from("x")), 1, 4, 1), // condition: x
            Token::new(TokenType::OpenCurly, 1, 6, 1),          // {
            Token::new(TokenType::Integer(1), 1, 7, 1),         // true branch: 1
            Token::new(TokenType::CloseCurly, 1, 9, 1),         // }
            Token::new(TokenType::ElseKeyword, 1, 11, 4),       // else
            Token::new(TokenType::OpenCurly, 1, 16, 1),         // {
            Token::new(TokenType::Integer(0), 1, 17, 1),        // false branch: 0
            Token::new(TokenType::CloseCurly, 1, 19, 1),        // }
        ]);

        let result = parser.parse_selection(Position::new(1, 1, 2));
        assert!(result.is_ok());
        let node = result.unwrap();

        // Assert that the created node matches the expected structure
        match node.node_type {
            ParseNodeType::IfElseStatement(condition, true_branch, false_branch) => {
                // Check condition
                match condition.node_type {
                    ParseNodeType::Identifier(name) => assert_eq!(name, "x"),
                    _ => panic!("Expected Identifier for condition"),
                }
                // Check true branch
                match true_branch.node_type {
                    ParseNodeType::IntegerLiteral(value) => assert_eq!(value, 1),
                    _ => panic!("Expected IntegerLiteral for true branch"),
                }
                // Check false branch
                match false_branch.node_type {
                    ParseNodeType::IntegerLiteral(value) => assert_eq!(value, 0),
                    _ => panic!("Expected IntegerLiteral for false branch"),
                }
            }
            _ => panic!("Expected IfElseStatement node"),
        }
    }

    #[test]
    #[should_panic]
    fn test_missing_else() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::IfKeyword, 1, 1, 2),          // if
            Token::new(TokenType::Identifier(String::from("x")), 1, 4, 1), // condition: x
            Token::new(TokenType::OpenCurly, 1, 6, 1),          // {
            Token::new(TokenType::Integer(1), 1, 7, 1),         // true branch: 1
            Token::new(TokenType::CloseCurly, 1, 9, 1),         // }
            // Missing else branch
        ]);

        parser.parse_selection(Position::new(1, 1, 2)).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_missing_true_branch() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::IfKeyword, 1, 1, 2),          // if
            Token::new(TokenType::Identifier(String::from("x")), 1, 4, 1), // condition: x
            Token::new(TokenType::OpenCurly, 1, 6, 1),          // {
            // Missing true branch
            Token::new(TokenType::CloseCurly, 1, 7, 1),         // }
            Token::new(TokenType::ElseKeyword, 1, 9, 4),        // else
            Token::new(TokenType::OpenCurly, 1, 14, 1),         // {
            Token::new(TokenType::Integer(0), 1, 15, 1),        // false branch: 0
            Token::new(TokenType::CloseCurly, 1, 17, 1),        // }
        ]);

        parser.parse_selection(Position::new(1, 1, 2)).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_missing_false_branch() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::IfKeyword, 1, 1, 2),          // if
            Token::new(TokenType::Identifier(String::from("x")), 1, 4, 1), // condition: x
            Token::new(TokenType::OpenCurly, 1, 6, 1),          // {
            Token::new(TokenType::Integer(1), 1, 7, 1),         // true branch: 1
            Token::new(TokenType::CloseCurly, 1, 9, 1),         // }
            Token::new(TokenType::ElseKeyword, 1, 11, 4),       // else
            Token::new(TokenType::OpenCurly, 1, 16, 1),         // {
            // Missing false branch
            Token::new(TokenType::CloseCurly, 1, 17, 1),        // }
        ]);

        parser.parse_selection(Position::new(1, 1, 2)).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_missing_condition() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::IfKeyword, 1, 1, 2),     // if
            // Missing condition
            Token::new(TokenType::OpenCurly, 1, 6, 1),     // {
            Token::new(TokenType::Integer(1), 1, 7, 1),    // true branch: 1
            Token::new(TokenType::CloseCurly, 1, 9, 1),    // }
            Token::new(TokenType::ElseKeyword, 1, 11, 4),  // else
            Token::new(TokenType::OpenCurly, 1, 16, 1),    // {
            Token::new(TokenType::Integer(0), 1, 17, 1),   // false branch: 0
            Token::new(TokenType::CloseCurly, 1, 19, 1),   // }
        ]);

        parser.parse_selection(Position::new(1, 1, 2)).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_invalid_token_in_condition() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::IfKeyword, 1, 1, 2),     // if
            Token::new(TokenType::ForKeyword, 1, 4, 3),    // Invalid condition token
            Token::new(TokenType::OpenCurly, 1, 6, 1),     // {
            Token::new(TokenType::Integer(1), 1, 7, 1),    // true branch: 1
            Token::new(TokenType::CloseCurly, 1, 9, 1),    // }
            Token::new(TokenType::ElseKeyword, 1, 11, 4),  // else
            Token::new(TokenType::OpenCurly, 1, 16, 1),    // {
            Token::new(TokenType::Integer(0), 1, 17, 1),   // false branch: 0
            Token::new(TokenType::CloseCurly, 1, 19, 1),   // }
        ]);

        parser.parse_selection(Position::new(1, 1, 2)).unwrap();
    }

    #[test]
    fn test_parse_identifier_as_variable() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::Identifier(String::from("my_variable")), 1, 1, 11), // my_variable
            Token::new(TokenType::Semicolon, 1, 12, 1),                              // ;
        ]);

        let result = parser.parse_identifier_or_function_call("my_variable", Position::new(1, 1, 11));
        assert!(result.is_ok());
        let node = result.unwrap();

        match node.node_type {
            ParseNodeType::Identifier(name) => assert_eq!(name, "my_variable"),
            _ => panic!("Expected Identifier node"),
        }
    }

    #[test]
    fn test_parse_identifier_as_function_call_with_no_params() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::Identifier(String::from("my_function")), 1, 1, 11), // my_function
            Token::new(TokenType::OpenParen, 1, 12, 1),                             // (
            Token::new(TokenType::CloseParen, 1, 13, 1),                            // )
            Token::new(TokenType::Semicolon, 1, 14, 1),                             // ;
        ]);

        let result = parser.parse_identifier_or_function_call("my_function", Position::new(1, 1, 11));
        assert!(result.is_ok());
        let node = result.unwrap();

        match node.node_type {
            ParseNodeType::FunctionCall(name, arguments) => {
                assert_eq!(name, "my_function");
                assert!(arguments.is_empty());
            }
            _ => panic!("Expected FunctionCall node"),
        }
    }

    #[test]
    fn test_parse_function_call_with_one_param() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::Identifier(String::from("my_function")), 1, 1, 11), // my_function
            Token::new(TokenType::OpenParen, 1, 12, 1),                             // (
            Token::new(TokenType::Integer(42), 1, 13, 2),                           // 42
            Token::new(TokenType::CloseParen, 1, 15, 1),                            // )
            Token::new(TokenType::Semicolon, 1, 16, 1),                             // ;
        ]);

        let result = parser.parse_identifier_or_function_call("my_function", Position::new(1, 1, 11)).unwrap();
        match result.node_type {
            ParseNodeType::FunctionCall(name, arguments) => {
                assert_eq!(name, "my_function");
                assert_eq!(arguments.len(), 1);
                match arguments[0].node_type {
                    ParseNodeType::IntegerLiteral(value) => assert_eq!(value, 42),
                    _ => panic!("Expected IntegerLiteral node for parameter"),
                }
            }
            _ => panic!("Expected FunctionCall node"),
        }
    }

    #[test]
    fn test_parse_function_call_with_multiple_params() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::Identifier(String::from("my_function")), 1, 1, 11), // my_function
            Token::new(TokenType::OpenParen, 1, 12, 1),                             // (
            Token::new(TokenType::Integer(42), 1, 13, 2),                           // 42
            Token::new(TokenType::Comma, 1, 15, 1),                                 // ,
            Token::new(TokenType::String(String::from("hello")), 1, 17, 7),  // "hello"
            Token::new(TokenType::CloseParen, 1, 24, 1),                            // )
            Token::new(TokenType::Semicolon, 1, 25, 1),                             // ;
        ]);

        let result = parser.parse_identifier_or_function_call("my_function", Position::new(1, 1, 11));
        assert!(result.is_ok());
        let node = result.unwrap();

        match node.node_type {
            ParseNodeType::FunctionCall(name, arguments) => {
                assert_eq!(name, "my_function");
                assert_eq!(arguments.len(), 2);

                // Check first argument
                match arguments[0].node_type {
                    ParseNodeType::IntegerLiteral(value) => assert_eq!(value, 42),
                    _ => panic!("Expected IntegerLiteral node for first parameter"),
                }

                // Check second argument
                match arguments[1].node_type.clone() {
                    ParseNodeType::StringLiteral(value) => assert_eq!(value, "hello"),
                    _ => panic!("Expected StringLiteral node for second parameter"),
                }
            }
            _ => panic!("Expected FunctionCall node"),
        }
    }

    #[test]
    fn test_parse_function_call_with_trailing_comma() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::Identifier(String::from("my_function")), 1, 1, 11), // my_function
            Token::new(TokenType::OpenParen, 1, 12, 1),                             // (
            Token::new(TokenType::Integer(42), 1, 13, 2),                           // 42
            Token::new(TokenType::Comma, 1, 15, 1),                                 // ,
            Token::new(TokenType::String(String::from("trailing")), 1, 17, 9), // "trailing"
            Token::new(TokenType::Comma, 1, 26, 1),                                 // ,
            Token::new(TokenType::CloseParen, 1, 27, 1),                            // )
            Token::new(TokenType::Semicolon, 1, 28, 1),                             // ;
        ]);

        parser.parse_identifier_or_function_call("my_function", Position::new(1, 1, 11)).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_parse_function_call_with_invalid_params() {
        let mut parser = Parser::new(vec![
            Token::new(TokenType::Identifier(String::from("my_function")), 1, 1, 11), // my_function
            Token::new(TokenType::OpenParen, 1, 12, 1),                             // (
            Token::new(TokenType::FnKeyword, 1, 13, 1),                               // Invalid token
            Token::new(TokenType::CloseParen, 1, 14, 1),                            // )
            Token::new(TokenType::Semicolon, 1, 15, 1),                             // ;
        ]);

        parser.parse_identifier_or_function_call("my_function", Position::new(1, 1, 11)).unwrap();
    }
}
