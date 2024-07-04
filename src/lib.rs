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

#[cfg(target_arch = "wasm32")]
use std::io::Write;
use std::path::Path;

use smol_str::SmolStr;

#[cfg(target_arch = "wasm32")]
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

#[cfg(not(target_arch = "wasm32"))]
fn parse_file<P: AsRef<Path> + Clone>(path: P, module: &SmolStr) -> ast::Module {
    let contents = std::fs::read_to_string(path.clone()).unwrap_or_else(|err| {
        panic!(
            "Unable to read file {} for module module {}: {}",
            path.as_ref().to_string_lossy(),
            module,
            err
        )
    });
    let tokens = scan(lex(&contents));
    let parser = TopDeclsParser::new();
    parser.parse(&(module.as_str().into()), tokens).unwrap()
}

#[cfg(target_arch = "wasm32")]
fn parse_file<P: AsRef<Path> + Clone>(_path: P, _module: &SmolStr) -> ast::Module {
    panic!();
}

#[cfg(target_arch = "wasm32")]
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

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "setupPanicHook")]
pub fn setup_panic_hook() {
    std::panic::set_hook(Box::new(hook_impl));
}

#[cfg(target_arch = "wasm32")]
fn hook_impl(info: &std::panic::PanicInfo) {
    add_interpreter_output("Panic:");
    add_interpreter_output(&info.to_string());
}

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "run")]
pub fn run_wasm(pgm: &str, input: &str) {
    clear_interpreter_output();
    clear_program_output();

    let tokens = scan(lex(pgm));
    let parser = TopDeclsParser::new();
    let module = parser.parse(&("FirWeb".into()), tokens).unwrap();
    let module = import_resolver::resolve_imports("", module);

    let mut w = WasmOutput;
    interpreter::run(&mut w, module, input.trim());
}

#[cfg(target_arch = "wasm32")]
struct WasmOutput;

#[cfg(target_arch = "wasm32")]
impl Write for WasmOutput {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        add_program_output(&String::from_utf8_lossy(buf));
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_expr_1() {
        let pgm = indoc::indoc! {"
            match t():
                X: 1
        "};
        let tokens = scan(lex(pgm));
        let ast = crate::parser::LExprParser::new()
            .parse(&"".into(), tokens)
            .unwrap();
        dbg!(ast);
    }

    #[test]
    fn parse_stmt_1() {
        let pgm = indoc::indoc! {"
            match t():
                X: 1
        "};
        let tokens = scan(lex(pgm));
        let ast = crate::parser::LStmtParser::new()
            .parse(&"".into(), tokens)
            .unwrap();
        dbg!(ast);
    }

    #[test]
    fn parse_fn_1() {
        let pgm = indoc::indoc! {"
            fn asdf() =
                let q = match t():
                    A.X: 1
                q
        "};
        let tokens = scan(lex(pgm));
        let ast = crate::parser::TopDeclsParser::new()
            .parse(&"".into(), tokens)
            .unwrap();
        dbg!(ast);

        let pgm = indoc::indoc! {"
            fn asdf() =
                let q = if A:
                    1
                else:
                    2
                q
        "};
        let tokens = scan(lex(pgm));
        let ast = crate::parser::TopDeclsParser::new()
            .parse(&"".into(), tokens)
            .unwrap();
        dbg!(ast);
    }
}
