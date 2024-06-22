mod ast;
mod collections;
mod interpolation;
mod interpreter;
mod lexer;
mod parser;
mod record_collector;
mod scanner;
mod scope_map;
mod token;

use lexer::lex;
use parser::*;
use scanner::scan;
use token::Token;

use std::io::Write;

use lexgen_util::Loc;
use wasm_bindgen::prelude::wasm_bindgen;

pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    let file = &args[1];
    let contents = std::fs::read_to_string(file).unwrap();

    let tokens: Vec<(Loc, Token, Loc)> = scan(&lex(&contents));
    let parser = TopDeclsParser::new();
    let decls: Vec<ast::L<ast::TopDecl>> = parser.parse(tokens).unwrap();

    let input = &args[2];
    let mut w = std::io::stdout();
    interpreter::run(&mut w, decls, input);
}

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);

    #[wasm_bindgen(js_name = "addInterpreterOutput")]
    fn add_interpreter_output(s: &str);

    #[wasm_bindgen(js_name = "clearInterpreterOutput")]
    fn clear_interpreter_output();

    #[wasm_bindgen(js_name = "addProgramOutput")]
    fn add_program_output(s: &str);

    #[wasm_bindgen(js_name = "clearProgramOutput")]
    fn clear_program_output();
}

#[wasm_bindgen(js_name = "run")]
pub fn run_wasm(pgm: &str, input: &str) {
    clear_interpreter_output();
    clear_program_output();

    let tokens: Vec<(Loc, Token, Loc)> = scan(&lex(pgm));
    let parser = TopDeclsParser::new();
    let decls: Vec<ast::L<ast::TopDecl>> = parser.parse(tokens).unwrap();

    let mut w = WasmOutput;
    interpreter::run(&mut w, decls, input.trim());
}

struct WasmOutput;

impl Write for WasmOutput {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        add_program_output(&String::from_utf8_lossy(buf));
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
