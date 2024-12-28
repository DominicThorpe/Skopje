use std::error::Error;
use indexmap::IndexMap;
use crate::errors::{ParsingError, SemanticError};
use crate::parsing::{ParseNode, ParseNodeType};
use crate::symbol_table::{SymbolTable, Type};


/// Represents operations that can be performed in binary or unary expressions.
///
/// This enum is used to describe mathematical or logical operations in the annotated syntax tree.
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


/// Represents the types of annotated nodes in the abstract syntax tree.
///
/// This enum encompasses all possible kinds of nodes that may appear in an annotated program. 
/// Each variant represents a specific type of syntax or construct in the program.
#[derive(Debug, Clone, PartialEq)]
pub enum AnnotatedNodeType {
    Program(Vec<AnnotatedNode>),
    Function(String, IndexMap<String, Type>, Type, Box<AnnotatedNode>),
    Loop(String, Type, Box<AnnotatedNode>, Box<AnnotatedNode>),
    IfElse(Box<AnnotatedNode>, Box<AnnotatedNode>, Box<AnnotatedNode>),
    Variable(String, Type, Box<AnnotatedNode>, Box<AnnotatedNode>),
    BinaryOp(Operation, Box<AnnotatedNode>, Box<AnnotatedNode>),
    UnaryOp(Operation, Box<AnnotatedNode>),
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
    pub fn annotate(&self, parse_tree: ParseNode, symbol_table: SymbolTable) -> Result<AnnotatedNode, Box<dyn Error>> {
        // Match against the type of the current parse node
        match parse_tree.node_type {
            // If the node represents a program, process all functions within it and collect them
            ParseNodeType::Program(functions) => {
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
            _ => Ok(AnnotatedNode::new(symbol_table, AnnotatedNodeType::Unit, (0, 0)))
        }
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
            Some(s) => Ok(AnnotatedNode::new(
                symbol_table.clone(),
                AnnotatedNodeType::Identifier(id.to_string()),
                (0, 0)
            ))
        }
    }
}
