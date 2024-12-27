#[derive(Debug, Clone, PartialEq)]
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


#[derive(Debug, Clone, PartialEq)]
pub struct SymbolTableEntry {
    name: String,
    symbol_type: Type,
    symbol_position: (usize, usize),
}


#[derive(Debug, Clone, PartialEq)]
pub struct SymbolTable {
    symbols: Vec<SymbolTableEntry>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self { symbols: Vec::new() }
    }
}
