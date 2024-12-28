use std::error::Error;
use indexmap::IndexMap;
use crate::errors::{ParsingError, SemanticError};
use crate::parsing::{ParseNode, ParseNodeType};
use crate::symbol_table::{SymbolTable, Type};


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


#[derive(Debug, Clone, PartialEq)]
pub struct AnnotatedNode {
    symbol_table: SymbolTable,
    node_type: AnnotatedNodeType,
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
    
    
    pub fn annotate(&self, parse_tree: ParseNode, symbol_table: SymbolTable) -> Result<AnnotatedNode, Box<dyn Error>> {
        match parse_tree.node_type {
            ParseNodeType::Program(functions) => {
                let node_type = AnnotatedNodeType::Program(
                    functions.into_iter().map(|f| self.annotate(f, symbol_table.clone()).unwrap()).collect());
                
                Ok(AnnotatedNode::new(
                    symbol_table.clone(),
                    node_type,
                    (parse_tree.position.line, parse_tree.position.col)
                ))
            }
            
            ParseNodeType::FunctionDeclaration(_, _, _, _) => 
                self.annotate_func_decl(parse_tree, symbol_table),
            
            ParseNodeType::IntegerLiteral(value) => Ok(AnnotatedNode::new(
                symbol_table.clone(), 
                AnnotatedNodeType::Int(value),
                (parse_tree.position.line, parse_tree.position.col)
            )),

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
