use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Hash)]
pub enum Type {
    /// The types of the parameters of the function, and the return type of the function
    Function(Vec<Type>, Box<Type>),
    UnsignedInt,
    SignedInt,
    Float,
    Bool,
    Char,
    /// The inner type of the array
    Array(Box<Type>),
}

impl Type {
    pub fn from_str(s: &str) -> Option<Type> {
        match s {
            "int" => Some(Type::SignedInt),
            "uint" => Some(Type::UnsignedInt),
            "float" => Some(Type::Float),
            "bool" => Some(Type::Bool),
            "char" => Some(Type::Char),
            "str" => Some(Type::Array(Box::new(Type::Char))),
            _ => None
        }
    }
}


#[derive(Debug, Clone, PartialEq, Hash)]
pub struct SymbolTableEntry {
    pub symbol_type: Type,
    pub symbol_position: (usize, usize),
}


#[derive(Debug, Clone, PartialEq)]
pub struct SymbolTable {
    symbols: HashMap<String, SymbolTableEntry>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self { symbols: HashMap::new() }
    }


    pub fn add_symbol(&mut self, name: String, symbol_type: Type, symbol_position: (usize, usize)) {
        self.symbols.insert(name, SymbolTableEntry { symbol_type, symbol_position });
    }
    
    
    pub fn add_symbols(&mut self, new_symbols: HashMap<String, SymbolTableEntry>) {
        self.symbols.extend(new_symbols);
    }


    pub fn get_symbol(&self, name: &str) -> Option<&SymbolTableEntry> {
        self.symbols.get(name)
    }


    pub fn get_symbol_type(&self, name: &str) -> Option<&Type> {
        match self.get_symbol(name) {
            Some(SymbolTableEntry { symbol_type, symbol_position }) => Some(symbol_type),
            None => None
        }
    }
}
