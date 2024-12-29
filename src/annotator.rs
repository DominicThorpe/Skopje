use std::collections::HashMap;
use std::error::Error;
use indexmap::IndexMap;
use crate::errors::{ParsingError, SemanticError};
use crate::parsing::{ParseNode, ParseNodeType};
use crate::symbol_table::{SymbolTable, SymbolTableEntry, Type};


/// Represents operations that can be performed in binary or unary expressions.
///
/// This enum is used to describe mathematical or logical operations in the annotated syntax tree.
#[allow(dead_code)]
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Operation {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Range
}


impl Operation {
    pub fn from_str(s: &str) -> Option<Operation> {
        match s { 
            "+" => Some(Operation::Add),
            "-" => Some(Operation::Sub),
            "*" => Some(Operation::Mul),
            "/" => Some(Operation::Div),
            "==" => Some(Operation::Eq),
            "!=" => Some(Operation::Neq),
            "::" => Some(Operation::Range),
            _ => None,
        }
    }
}


/// Represents the types of annotated nodes in the abstract syntax tree.
///
/// This enum encompasses all possible kinds of nodes that may appear in an annotated program. 
/// Each variant represents a specific type of syntax or construct in the program.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub enum AnnotatedNodeType {
    Program(Vec<AnnotatedNode>),
    Function(String, IndexMap<String, Type>, Type, Box<AnnotatedNode>),
    FunctionCall(String, Vec<AnnotatedNode>),
    Loop(String, Type, Box<AnnotatedNode>, Box<AnnotatedNode>),
    IfElse(Box<AnnotatedNode>, Box<AnnotatedNode>, Box<AnnotatedNode>),
    Variable(String, Type, Box<AnnotatedNode>, Box<AnnotatedNode>),
    BinaryOp(Operation, Box<AnnotatedNode>, Box<AnnotatedNode>),
    UnaryOp(Operation, Box<AnnotatedNode>),
    ArrayIndexOp(Box<AnnotatedNode>, Box<AnnotatedNode>),
    Float(f64),
    Int(u64),
    String(String),
    Bool(bool),
    Char(char),
    Identifier(String),
    Array(Box<AnnotatedNode>),
    Unit
}


/// Represents a single annotated node in the abstract syntax tree.
///
/// An annotated node pairs a piece of syntax (represented by `AnnotatedNodeType`) with additional 
/// semantic information, such as its position in the code and its associated symbol table.
#[derive(Debug, Clone, PartialEq)]
pub struct AnnotatedNode {
    /// The symbol table for this node, describing the variables, functions, and other
    /// symbols in scope at this point in the program.
    symbol_table: SymbolTable,
    /// The type of the node, describing the kind of syntax it represents.
    node_type: AnnotatedNodeType,
    /// The position of the node in the source code, represented as a tuple `(line, column)`.
    position: (usize, usize),
}


impl AnnotatedNode {
    pub fn new(symbol_table: SymbolTable, node_type: AnnotatedNodeType, position: (usize, usize)) -> Self {
        Self { symbol_table, node_type, position }
    }
}


#[derive(Debug, Clone, PartialEq)]
pub struct Annotator {}


impl Annotator {
    pub fn new() -> Self {
        Self {}
    }


    /// Recursively annotates a parse tree and converts it into an annotated syntax tree.
    ///
    /// This function traverses the given `parse_tree` and transforms it into an `AnnotatedNode`,
    /// enhancing the syntax tree with semantic information (e.g., type annotations, symbol table) and
    /// position details. The annotation process may involve resolving variable identifiers,
    /// determining types of expressions, and refining structures based on semantic rules.
    ///
    /// # Parameters
    /// - `parse_tree`: A `ParseNode` representing the root of the parse tree to be annotated.
    /// - `symbol_table`: A `SymbolTable` containing the symbols and their types in the current scope.
    ///
    /// # Returns
    /// - `Ok(AnnotatedNode)`: The resulting annotated node if the parse tree is successfully processed.
    /// - `Err(Box<dyn Error>)`: An error if the annotation process encounters an issue, such as
    ///   undefined symbols, invalid types, or unexpected parse nodes.
    ///
    /// # Behavior
    /// - Handles various `ParseNodeType` cases:
    ///   - **Program**: Processes a collection of function nodes and returns an `AnnotatedNodeType::Program`.
    ///   - **FunctionDeclaration**: Delegates to `annotate_func_decl` to handle function-specific annotation.
    ///   - **IntegerLiteral**: Converts integer parse nodes into `AnnotatedNodeType::Int`.
    ///   - **Identifier**: Looks up symbols in the `SymbolTable` and returns annotated identifiers.
    ///   - **Other Node Types**: Returns a default `AnnotatedNode` with a `Unit` type.
    ///
    /// # Example
    /// ```rust
    /// let parse_tree = ParseNode {
    ///     node_type: ParseNodeType::IntegerLiteral(42),
    ///     position: (1, 5),
    /// };
    /// let symbol_table = SymbolTable::new();
    /// let annotator = Annotator::new();
    /// let result = annotator.annotate(parse_tree, symbol_table);
    /// assert!(result.is_ok());
    /// let annotated_node = result.unwrap();
    /// assert!(matches!(annotated_node.node_type, AnnotatedNodeType::Int(42)));
    /// ```
    pub fn annotate(&self, parse_tree: ParseNode, mut symbol_table: SymbolTable) -> Result<AnnotatedNode, Box<dyn Error>> {
        // Match against the type of the current parse node
        match parse_tree.node_type {
            // If the node represents a program, process all functions within it and collect them
            ParseNodeType::Program(functions) => {
                symbol_table.add_symbols(self.get_function_types(&functions, symbol_table.clone())?);
                let node_type = AnnotatedNodeType::Program(
                    functions.into_iter().map(|f| self.annotate(f, symbol_table.clone()).unwrap()).collect());
                
                Ok(AnnotatedNode::new(
                    symbol_table.clone(),
                    node_type,
                    (parse_tree.position.line, parse_tree.position.col)
                ))
            }

            // Handle function declarations by delegating to `annotate_func_decl`
            ParseNodeType::FunctionDeclaration(_, _, _, _) => 
                self.annotate_func_decl(parse_tree, symbol_table),

            // Handle integer literals, converting them into a `AnnotatedNodeType::Int`
            ParseNodeType::IntegerLiteral(value) => Ok(AnnotatedNode::new(
                symbol_table.clone(), 
                AnnotatedNodeType::Int(value),
                (parse_tree.position.line, parse_tree.position.col)
            )),

            // Handle identifiers by finding their corresponding symbols in the symbol table
            ParseNodeType::Identifier(id) => self.get_annotated_id(id.as_str(), &symbol_table),
            
            ParseNodeType::FunctionCall(name, args) => {
                let annotated_node_type = AnnotatedNodeType::FunctionCall(
                    name,
                    args.into_iter().map(|arg| self.annotate(arg, symbol_table.clone()).unwrap()).collect()
                );
                
                Ok(AnnotatedNode::new(
                    symbol_table.clone(),
                    annotated_node_type,
                    (parse_tree.position.line, parse_tree.position.col)
                ))
            },
            
            ParseNodeType::BinaryOperation(op, left, right) => { 
                let op = match Operation::from_str(op.as_str()) {
                    Some(op ) => op,
                    None => return Err(Box::new(SemanticError::UnknownOperation(op, 0, 0)))
                };
                
                let left = self.annotate(*left, symbol_table.clone())?;
                let right = self.annotate(*right, symbol_table.clone())?;
                let left_position = left.position; 
                let node_type = AnnotatedNodeType::BinaryOp(op, Box::new(left), Box::new(right));
                Ok(AnnotatedNode::new(symbol_table, node_type, left_position))
            },
            
            ParseNodeType::UnaryOperation(op, operand) => {
                let op = match Operation::from_str(op.as_str()) {
                    Some(op) => op,
                    None => return Err(Box::new(SemanticError::UnknownOperation(op, 0, 0)))
                };
                
                let operand = self.annotate(*operand, symbol_table.clone())?;
                let op_pos = operand.position;
                let node_type = AnnotatedNodeType::UnaryOp(op, Box::new(operand));
                Ok(AnnotatedNode::new(symbol_table, node_type, op_pos))
            },
            
            ParseNodeType::ArrayIndexOperation(array, index) => {
                let array = self.annotate(*array, symbol_table.clone())?;
                let index = self.annotate(*index, symbol_table.clone())?;
                let array_pos = array.position;
                let node_type = AnnotatedNodeType::ArrayIndexOp(Box::new(array), Box::new(index));
                Ok(AnnotatedNode::new(symbol_table, node_type, array_pos))
            }
            
            other => unimplemented!("{:?} is not yet supported", other),
        }
    }


    /// Extracts and constructs function types along with their symbol table entries from the parse nodes.
    ///
    /// This function processes a list of function declarations, extracting parameter types and return types to
    /// construct a mapping of function names to their corresponding `SymbolTableEntry`. The `SymbolTableEntry`
    /// includes the function's type and its position in the source code.
    ///
    /// # Parameters
    /// - `funcs`: A vector of `ParseNode` representing function declarations.
    /// - `symbol_table`: The current symbol table for type resolution.
    ///
    /// # Returns
    /// - `Ok(HashMap<String, SymbolTableEntry>)` on success.
    /// - `Err(Box<dyn Error>)` if type annotation or parsing fails.
    ///
    /// # Errors
    /// - Returns an error if an unexpected parse node type is encountered or type resolution fails.
    fn get_function_types(&self, funcs: &[ParseNode], symbol_table: SymbolTable) -> Result<HashMap<String, SymbolTableEntry>, Box<dyn Error>> {
        // Initialize a HashMap to store function name and their symbol table entry.
        let mut func_types: HashMap<String, SymbolTableEntry> = HashMap::with_capacity(funcs.len());

        for func in funcs {
            // Extract the position of the function for error reporting.
            let (line, col) = (func.position.line, func.position.col);

            // Ensure the node is a function declaration to proceed.
            match &func.node_type {
                ParseNodeType::FunctionDeclaration(name, params, _, return_type_node) => {
                    // Extract parameter types and handle potential errors upfront.
                    let param_types = params
                        .iter()
                        .map(|param| match &param.node_type {
                            ParseNodeType::FunctionParameter(_, param_type) =>
                                self.get_annotated_type(*param_type.clone(), symbol_table.clone()),
                            _ => panic!(),
                        })
                        .collect::<Result<Vec<_>, _>>()?;

                    // Resolve the return type.
                    let return_type = self.get_annotated_type(
                        *return_type_node.clone(), 
                        symbol_table.clone()
                    )?;

                    // Create a function type and store it in the HashMap.
                    let func_type = Type::Function(param_types, Box::new(return_type));
                    func_types.insert(
                        name.clone(),
                        SymbolTableEntry {
                            symbol_type: func_type,
                            symbol_position: (line, col),
                        },
                    );
                }
                // If the node isn't a valid function declaration, return a detailed error.
                node => {
                    return Err(Box::new(ParsingError::UnexpectedParseNode(
                        node.clone(),
                        func.position.line,
                        func.position.col,
                    )));
                }
            }
        }

        // Return the constructed function type mappings.
        Ok(func_types)
    }
    
    
    fn annotate_func_decl(&self, parse_tree: ParseNode, symbol_table: SymbolTable) -> Result<AnnotatedNode, Box<dyn Error>> {
        let (name, params, body, rt) = match parse_tree.node_type {
            ParseNodeType::FunctionDeclaration(name, params, body, rt) => (name, params, body, rt),
            other => return Err(Box::new(ParsingError::UnexpectedParseNode(other, parse_tree.position.line, parse_tree.position.col)))
        };
        
        let mut new_symbol_table = symbol_table.clone();
        let params: IndexMap<String, Type> = params.into_iter()
            .map(|p| match p.node_type {
                ParseNodeType::FunctionParameter(s, t) => {
                    let annotated_type = self.get_annotated_type(*t, symbol_table.clone()).unwrap();
                    let (p_line, p_col) = (p.position.line, p.position.col);
                    new_symbol_table.add_symbol(s.clone(), annotated_type.clone(), (p_line, p_col));
                    Ok((s, annotated_type))
                },

                other => Err(Box::new(ParsingError::UnexpectedParseNode(
                    other, p.position.line, p.position.col
                ))),
            })
            .collect::<Result<_, Box<ParsingError>>>()?;
        
        let return_type: Type = self.get_annotated_type(*rt, symbol_table.clone())?;
        let body: AnnotatedNode = self.annotate(*body, new_symbol_table)?;
        let node_type = AnnotatedNodeType::Function(name, params, return_type, Box::new(body));
        Ok(AnnotatedNode::new(symbol_table, node_type, (parse_tree.position.line, parse_tree.position.col)))
    }
    
    
    fn get_annotated_type(&self, parse_tree: ParseNode, symbol_table: SymbolTable) -> Result<Type, Box<dyn Error>> {
        match parse_tree.node_type {
            ParseNodeType::ArrayType(inner_type) => 
                Ok(Type::Array(Box::new(self.get_annotated_type(*inner_type, symbol_table.clone())?))),
            
            ParseNodeType::Identifier(name) => match Type::from_str(name.as_str()) {
                Some(t) => Ok(t),
                None => Err(Box::new(SemanticError::InvalidType(
                    name, parse_tree.position.line, parse_tree.position.col
                )))
            }, 
            
            other => Err(Box::new(ParsingError::UnexpectedParseNode(
                other, parse_tree.position.line, parse_tree.position.col
            )))
        }
    }


    fn get_annotated_id(&self, id: &str, symbol_table: &SymbolTable) -> Result<AnnotatedNode, Box<dyn Error>> {
        match symbol_table.get_symbol(id) {
            None => Err(Box::new(SemanticError::UnknownSymbol(id.to_string(), 0, 0))),
            Some(_) => Ok(AnnotatedNode::new(
                symbol_table.clone(),
                AnnotatedNodeType::Identifier(id.to_string()),
                (0, 0)
            ))
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::parsing::{ParseNodeType, ParseNode};
    use crate::symbol_table::{SymbolTable, Type};
    use crate::lexing::{Lexer, Position};
    use crate::parsing;

    #[test]
    fn test_get_function_types_success() {
        let annotator = Annotator::new();
        // Construct a function declaration ParseNode to test against
        let func_node = ParseNode {
            node_type: ParseNodeType::FunctionDeclaration(
                "test_function".to_string(),
                vec![
                    ParseNode {
                        node_type: ParseNodeType::FunctionParameter(
                            "x".to_string(),
                            Box::new(ParseNode {
                                node_type: ParseNodeType::Identifier("int".to_string()),
                                position: Position::zeros(),
                            }),
                        ),
                        position: Position::zeros(),
                    },
                ],
                Box::new(ParseNode {
                    node_type: ParseNodeType::IntegerLiteral(42),
                    position: Position::zeros(),
                }),
                Box::new(ParseNode {
                    node_type: ParseNodeType::Identifier("int".to_string()),
                    position: Position::zeros(),
                }),
            ),
            position: Position::zeros(),
        };

        let symbol_table = SymbolTable::new();

        // Call get_function_types
        let result = annotator.get_function_types(&[func_node], symbol_table);

        // Assert the result is Ok and check the contents
        assert!(result.is_ok());
        let func_types = result.unwrap();
        assert!(func_types.contains_key("test_function"));
        let entry = func_types["test_function"].clone();
        if let Type::Function(param_types, return_type) = entry.symbol_type {
            assert_eq!(param_types.len(), 1);
            assert_eq!(param_types[0], Type::SignedInt);
            assert_eq!(*return_type, Type::SignedInt);
        } else {
            panic!("Expected function type, got: {:?}", entry.symbol_type);
        }
    }

    #[test]
    fn test_get_function_types_unexpected_node() {
        let annotator = Annotator::new();
        let invalid_node = ParseNode {
            node_type: ParseNodeType::IntegerLiteral(42),
            position: Position::zeros(),
        };
        let symbol_table = SymbolTable::new();

        // Call get_function_types and assert it returns an error
        let result = annotator.get_function_types(&[invalid_node], symbol_table);
        assert!(result.is_err());
    }

    #[test]
    fn test_annotate_program() {
        let annotator = Annotator::new();
        let program_node = ParseNode {
            node_type: ParseNodeType::Program(vec![
                ParseNode {
                    node_type: ParseNodeType::FunctionDeclaration(
                        "main".to_string(),
                        vec![],
                        Box::new(ParseNode {
                            node_type: ParseNodeType::IntegerLiteral(1),
                            position: Position::zeros(),
                        }),
                        Box::new(ParseNode {
                            node_type: ParseNodeType::Identifier("int".to_string()),
                            position: Position::zeros(),
                        }),
                    ),
                    position: Position::zeros(),
                },
            ]),
            position: Position::zeros(),
        };
        let symbol_table = SymbolTable::new();

        // Call annotate
        let result = annotator.annotate(program_node, symbol_table);

        // Assert the program was annotated correctly
        assert!(result.is_ok());
        let annotated_program = result.unwrap();
        assert!(matches!(
            annotated_program.node_type,
            AnnotatedNodeType::Program(_)
        ));
    }

    #[test]
    fn test_annotate_integer_literal() {
        let annotator = Annotator::new();
        let integer_node = ParseNode {
            node_type: ParseNodeType::IntegerLiteral(100),
            position: Position::zeros(),
        };
        let symbol_table = SymbolTable::new();

        // Call annotate
        let result = annotator.annotate(integer_node, symbol_table);

        // Assert the integer literal was annotated correctly
        assert!(result.is_ok());
        let annotated_node = result.unwrap();
        assert!(matches!(
            annotated_node.node_type,
            AnnotatedNodeType::Int(value) if value == 100
        ));
    }

    #[test]
    fn test_annotate_function() {
        let annotator = Annotator::new();
        let func_node = ParseNode {
            node_type: ParseNodeType::FunctionDeclaration(
                "test".to_string(),
                vec![
                    ParseNode {
                        node_type: ParseNodeType::FunctionParameter(
                            "x".to_string(),
                            Box::new(ParseNode {
                                node_type: ParseNodeType::Identifier("int".to_string()),
                                position: Position::zeros(),
                            }),
                        ),
                        position: Position::zeros(),
                    },
                ],
                Box::new(ParseNode {
                    node_type: ParseNodeType::IntegerLiteral(1),
                    position: Position::zeros(),
                }),
                Box::new(ParseNode {
                    node_type: ParseNodeType::Identifier("int".to_string()),
                    position: Position::zeros(),
                }),
            ),
            position: Position::zeros(),
        };
        let symbol_table = SymbolTable::new();

        // Call annotate
        let result = annotator.annotate(func_node, symbol_table);

        // Assert the function was annotated correctly
        assert!(result.is_ok());
        let annotated_function = result.unwrap();
        assert!(matches!(
            annotated_function.node_type,
            AnnotatedNodeType::Function(_, _, _, _)
        ));
    }

    #[test]
    #[should_panic]
    fn test_annotate_unhandled_node() {
        let annotator = Annotator::new();
        let unknown_node = ParseNode {
            node_type: ParseNodeType::ArrayType(Box::new(ParseNode {
                node_type: ParseNodeType::Identifier("unknown".to_string()),
                position: Position::zeros(),
            })),
            position: Position::zeros(),
        };
        let symbol_table = SymbolTable::new();

        // Call annotate
        let result = annotator.annotate(unknown_node, symbol_table);
        result.unwrap();
    }

    #[test]
    fn test_get_annotated_type_success() {
        let annotator = Annotator::new();
        let type_node = ParseNode {
            node_type: ParseNodeType::Identifier("int".to_string()),
            position: Position::zeros(),
        };
        let symbol_table = SymbolTable::new();

        // Call get_annotated_type
        let result = annotator.get_annotated_type(type_node, symbol_table);

        // Assert type is correctly resolved
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Type::SignedInt);
    }

    #[test]
    fn test_get_annotated_type_error() {
        let annotator = Annotator::new();
        let invalid_node = ParseNode {
            node_type: ParseNodeType::Identifier("unknown_type".to_string()),
            position: Position::zeros(),
        };
        let symbol_table = SymbolTable::new();

        // Call get_annotated_type and expect an error
        let result = annotator.get_annotated_type(invalid_node, symbol_table);
        assert!(result.is_err());
    }

    #[test]
    fn test_annotate_unary_operation() {
        let annotator = Annotator::new();
        let unary_node = ParseNode {
            node_type: ParseNodeType::UnaryOperation(
                "-".to_string(),
                Box::new(ParseNode {
                    node_type: ParseNodeType::IntegerLiteral(42),
                    position: Position::zeros(),
                }),
            ),
            position: Position::zeros(),
        };
        let symbol_table = SymbolTable::new();

        // Call annotate
        let result = annotator.annotate(unary_node, symbol_table);

        // Assert the unary operation was annotated correctly
        assert!(result.is_ok());
    }

    #[test]
    fn test_annotate_binary_operation() {
        let annotator = Annotator::new();
        let binary_node = ParseNode {
            node_type: ParseNodeType::BinaryOperation(
                "+".to_string(),
                Box::new(ParseNode {
                    node_type: ParseNodeType::IntegerLiteral(10),
                    position: Position::zeros(),
                }),
                Box::new(ParseNode {
                    node_type: ParseNodeType::IntegerLiteral(20),
                    position: Position::zeros(),
                }),
            ),
            position: Position::zeros(),
        };
        let symbol_table = SymbolTable::new();

        // Call annotate
        let result = annotator.annotate(binary_node, symbol_table);

        // Assert the binary operation was annotated correctly
        assert!(result.is_ok());
    }

    #[test]
    fn test_annotate_array_index_operation() {
        let mut lexer = Lexer::new("fn main(arr: [int]) -> int { arr[1] }".to_string());
        lexer.lex().unwrap();

        let mut parser = parsing::Parser::new(lexer.tokens);
        let parse_tree = parser.parse().unwrap();
        let result = Annotator::new().annotate(parse_tree.clone(), SymbolTable::new());

        // Assert the array index operation was annotated correctly
        assert!(result.is_ok());
    }
}
