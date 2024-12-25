mod lexing;
mod errors;
mod parsing;

fn main() {
    let mut lexer = lexing::Lexer::new("
fn main() -> int {
    foo(1, 3, b)
}
".to_string());
    lexer.lex().unwrap();
    
    let mut parser = parsing::Parser::new(lexer.tokens);
    let parse_tree = parser.parse().unwrap();
    
    println!("{:#?}", parse_tree);
}


