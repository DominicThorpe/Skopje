use crate::annotator::Annotator;
use crate::symbol_table::SymbolTable;

mod lexing;
mod errors;
mod parsing;
mod symbol_table;
mod annotator;

fn main() {
    let mut lexer = lexing::Lexer::new("
fn main() -> [int] {
    1
}
".to_string());
    lexer.lex().unwrap();
    
    let mut parser = parsing::Parser::new(lexer.tokens);
    let parse_tree = parser.parse().unwrap();
    let annotated_tree = Annotator::new().annotate(parse_tree, SymbolTable::new()).unwrap();
    
    println!("{:#?}", annotated_tree);
}


