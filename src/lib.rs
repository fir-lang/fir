mod ast;
mod collections;
mod import_resolver;
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
use std::path::Path;

use lexgen_util::Loc;
use smol_str::SmolStr;
use wasm_bindgen::prelude::wasm_bindgen;

pub fn main() {
    let args: Vec<String> = std::env::args().collect();

    let file_path = Path::new(&args[1]); // "examples/Foo.fir"
    let file_name_wo_ext = file_path.file_stem().unwrap(); // "Foo"
    let root_path = file_path.parent().unwrap(); // "examples/"

    let module = parse_file(file_path, &SmolStr::new(file_name_wo_ext.to_str().unwrap()));
    let module = import_resolver::resolve_imports(root_path.to_str().unwrap(), module);

    let input = &args[2];
    let mut w = std::io::stdout();
    interpreter::run(&mut w, module, input);
}

fn parse_file<P: AsRef<Path> + Clone>(path: P, module: &SmolStr) -> ast::Module {
    let contents = std::fs::read_to_string(path.clone()).unwrap_or_else(|err| {
        panic!(
            "Unable to read file {} for module module {}: {}",
            path.as_ref().to_string_lossy(),
            module,
            err
        )
    });
    let tokens = scan(crate::lexer::lex(&contents));
    let parser = TopDeclsParser::new();
    parser.parse(&(module.as_str().into()), tokens).unwrap()
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

    let tokens: Vec<(Loc, Token, Loc)> = scan(lex(pgm));
    let parser = TopDeclsParser::new();
    let decls: Vec<ast::L<ast::TopDecl>> = parser.parse(&("TODO".into()), tokens).unwrap();

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
