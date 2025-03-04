use std::io::{self, stdin, stdout, Write};

use lexer::Lexer;

mod codegen;
mod error;
mod lexer;
mod parser;

fn main() -> io::Result<()> {
    loop {
        let mut input = String::new();
        print!(">");
        stdout().flush()?;
        stdin().read_line(&mut input)?;
        input = input.trim().to_string();

        if input == "exit" {
            break;
        }

        match parser::parse(&mut Lexer::new(&input).peekable()) {
            Ok(ast) => println!("{}", codegen::gen(ast)),
            Err(err) => println!("Err: {}", err),
        }
    }

    Ok(())
}
