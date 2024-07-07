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

use lexgen_util::Loc;
use smol_str::SmolStr;

fn lexgen_loc_string(module: &SmolStr, lexgen_loc: lexgen_util::Loc) -> String {
    format!("{}:{}:{}", module, lexgen_loc.line + 1, lexgen_loc.col + 1)
}

fn parse_module(module: &SmolStr, tokens: Vec<(Loc, token::Token, Loc)>) -> ast::Module {
    let parser = parser::TopDeclsParser::new();
    match parser.parse(&(module.as_str().into()), tokens) {
        Ok(ast) => ast,
        Err(err) => match err {
            lalrpop_util::ParseError::InvalidToken { location } => {
                panic!("Invalid token at {}", lexgen_loc_string(module, location));
            }

            lalrpop_util::ParseError::UnrecognizedEof {
                location,
                expected: _,
            } => {
                panic!("Unexpected EOF at {}", lexgen_loc_string(module, location));
            }

            lalrpop_util::ParseError::UnrecognizedToken { token, expected: _ } => {
                panic!(
                    "Unexpected token {:?} at {}",
                    token.1,
                    lexgen_loc_string(module, token.0)
                );
            }

            lalrpop_util::ParseError::ExtraToken { token } => {
                panic!(
                    "Extra token {:?} after parsing at {}",
                    token.1,
                    lexgen_loc_string(module, token.0)
                );
            }

            lalrpop_util::ParseError::User { error } => {
                panic!("Lexer error: {:?}", error)
            }
        },
    }
}

#[cfg(not(target_arch = "wasm32"))]
mod native {
    use super::*;

    use smol_str::SmolStr;
    use std::path::Path;

    pub fn main() {
        let fir_root = match std::env::var("FIR_ROOT") {
            Ok(s) => s,
            Err(_) => {
                eprintln!("Fir uses FIR_ROOT environment variable to find standard libraries.");
                eprintln!("Please set FIR_ROOT to Fir git repo root.");
                std::process::exit(1);
            }
        };

        let args: Vec<String> = std::env::args().collect();

        let file_path = Path::new(&args[1]); // "examples/Foo.fir"
        let file_name_wo_ext = file_path.file_stem().unwrap(); // "Foo"
        let root_path = file_path.parent().unwrap(); // "examples/"

        let module = parse_file(file_path, &SmolStr::new(file_name_wo_ext.to_str().unwrap()));
        let module =
            import_resolver::resolve_imports(&fir_root, root_path.to_str().unwrap(), module);

        let input = args.get(2).map(|s| s.as_str()).unwrap_or("");
        let mut w = std::io::stdout();
        interpreter::run(&mut w, module, input);
    }

    pub fn parse_file<P: AsRef<Path> + Clone>(path: P, module: &SmolStr) -> ast::Module {
        let contents = std::fs::read_to_string(path.clone()).unwrap_or_else(|err| {
            panic!(
                "Unable to read file {} for module module {}: {}",
                path.as_ref().to_string_lossy(),
                module,
                err
            )
        });
        let tokens = scanner::scan(lexer::lex(&contents));
        parse_module(module, tokens)
    }
}

#[cfg(not(target_arch = "wasm32"))]
pub use native::{main, parse_file};

#[cfg(target_arch = "wasm32")]
mod wasm {
    use super::*;

    use std::io::Write;
    use std::path::Path;

    use smol_str::SmolStr;
    use wasm_bindgen::prelude::wasm_bindgen;
    use web_sys::XmlHttpRequest;

    pub fn parse_file<P: AsRef<Path> + Clone>(path: P, module: &SmolStr) -> ast::Module {
        let path = path.as_ref().to_string_lossy();
        match fetch_sync(&path) {
            Some(contents) => {
                let tokens = scanner::scan(lexer::lex(&contents));
                parse_module(module, tokens)
            }
            None => {
                panic!("Unable to fetch {}", path);
            }
        }
    }

    fn fetch_sync(url: &str) -> Option<String> {
        let xhr = XmlHttpRequest::new().unwrap();
        xhr.open_with_async("GET", url, false).unwrap(); // false makes it synchronous

        xhr.send().unwrap();

        if xhr.status() == Ok(200) {
            let response_text = xhr.response_text().unwrap().unwrap();
            Some(response_text)
        } else {
            None
        }
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

    #[wasm_bindgen(js_name = "setupPanicHook")]
    pub fn setup_panic_hook() {
        std::panic::set_hook(Box::new(hook_impl));
    }

    fn hook_impl(info: &std::panic::PanicInfo) {
        add_interpreter_output("Panic:");
        add_interpreter_output(&info.to_string());
    }

    #[wasm_bindgen(js_name = "run")]
    pub fn run_wasm(pgm: &str, input: &str) {
        clear_interpreter_output();
        clear_program_output();

        let tokens = scanner::scan(lexer::lex(pgm));
        let module = parse_module(&SmolStr::new("FirWeb"), tokens);
        let module = import_resolver::resolve_imports("fir", "", module);

        let mut w = WasmOutput;
        interpreter::run(&mut w, module, input.trim());
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
}

#[cfg(target_arch = "wasm32")]
pub use wasm::parse_file;

#[cfg(test)]
mod tests {
    use crate::lexer::lex;
    use crate::scanner::scan;

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
