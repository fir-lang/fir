#![allow(
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::large_enum_variant
)]

mod ast;
mod collections;
mod import_resolver;
mod interpolation;
mod interpreter;
mod lexer;
mod lowering;
mod mono_ast;
mod monomorph;
mod parser;
mod parser_utils;
mod record_collector;
mod scanner;
mod scope_map;
mod token;
mod type_checker;
mod utils;

use lexgen_util::Loc;
use smol_str::SmolStr;

#[derive(Debug, Clone)]
pub struct CompilerOpts {
    pub typecheck: bool,
    pub no_prelude: bool,
    pub no_backtrace: bool,
    pub print_tokens: bool,
    pub print_parsed_ast: bool,
    pub print_checked_ast: bool,
    pub print_mono_ast: bool,
    pub print_lowered_ast: bool,
    pub main: String,
    pub import_paths: collections::Map<String, String>,
}

fn lexgen_loc_display(module: &SmolStr, lexgen_loc: lexgen_util::Loc) -> String {
    format!("{}:{}:{}", module, lexgen_loc.line + 1, lexgen_loc.col + 1)
}

fn parse_module(module: &SmolStr, contents: &str, print_tokens: bool) -> ast::Module {
    let tokens = combine_uppercase_lbrackets(scanner::scan(
        lexer::lex(contents, module).into_iter(),
        module,
    ));
    // dbg!(tokens.iter().map(|(_, t, _)| t.clone()).collect::<Vec<_>>());

    if print_tokens {
        for (l, t, _) in &tokens {
            println!(
                "{}:{}:{}: {:?} {:?}",
                module,
                l.line + 1,
                l.col + 1,
                t.kind,
                t.text
            );
        }
    }

    let parser = parser::TopDeclsParser::new();
    match parser.parse(&(module.as_str().into()), tokens) {
        Ok(ast) => ast,
        Err(err) => report_parse_error(module, err),
    }
}

fn report_parse_error(
    module: &SmolStr,
    err: lalrpop_util::ParseError<
        Loc,
        token::Token,
        lexgen_util::LexerError<std::convert::Infallible>,
    >,
) -> ! {
    match err {
        lalrpop_util::ParseError::InvalidToken { location } => {
            panic!("{}: Invalid token", lexgen_loc_display(module, location));
        }

        lalrpop_util::ParseError::UnrecognizedEof {
            location,
            expected: _,
        } => {
            panic!("{}: Unexpected EOF", lexgen_loc_display(module, location));
        }

        lalrpop_util::ParseError::UnrecognizedToken { token, expected: _ } => {
            panic!(
                "{}: Unexpected token {:?} (\"{}\")",
                lexgen_loc_display(module, token.0),
                token.1.kind,
                token.1.text,
            );
        }

        lalrpop_util::ParseError::ExtraToken { token } => {
            panic!(
                "{}: Extra token {:?} after parsing",
                lexgen_loc_display(module, token.0),
                token.1,
            );
        }

        lalrpop_util::ParseError::User { error } => {
            panic!("Lexer error: {:?}", error)
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
mod native {
    use super::*;

    use smol_str::SmolStr;
    use std::path::Path;

    pub fn main(mut opts: CompilerOpts, program: String, mut program_args: Vec<String>) {
        let fir_root = match std::env::var("FIR_ROOT") {
            Ok(fir_root) => {
                let mut path = std::path::PathBuf::new();
                path.push(fir_root);
                path.push("lib");
                path.to_string_lossy().to_string()
            }
            Err(_) => {
                eprintln!("Fir uses FIR_ROOT environment variable to find standard libraries.");
                eprintln!("Please set FIR_ROOT to Fir git repo root.");
                std::process::exit(1);
            }
        };

        let old_fir_root = opts
            .import_paths
            .insert("Fir".to_string(), fir_root.clone());
        if old_fir_root.is_some() {
            eprintln!(
                "WARNING: Fir root specified multiple times. Using {} as root.",
                fir_root
            );
        }

        if opts.no_backtrace {
            std::panic::set_hook(Box::new(|panic_info| {
                if let Some(s) = panic_info.payload().downcast_ref::<String>() {
                    eprintln!("{}", s);
                } else if let Some(s) = panic_info.payload().downcast_ref::<&str>() {
                    eprintln!("{}", s);
                } else {
                    eprintln!("Weird panic payload in panic handler");
                }
            }));
        }

        let file_path = Path::new(&program); // "examples/Foo.fir"
        let file_name_wo_ext = file_path.file_stem().unwrap(); // "Foo"
        let root_path = file_path.parent().unwrap(); // "examples/"

        let module = parse_file(
            file_path,
            &SmolStr::new(file_name_wo_ext.to_str().unwrap()),
            opts.print_tokens,
        );
        let mut module = import_resolver::resolve_imports(
            &opts.import_paths,
            root_path.to_str().unwrap(),
            module,
            !opts.no_prelude, // import_prelude
            opts.print_tokens,
        );

        if opts.print_parsed_ast {
            ast::printer::print_module(&module);
        }

        type_checker::check_module(&mut module, &fir_root);

        if opts.print_checked_ast {
            ast::printer::print_module(&module);
        }

        if opts.typecheck {
            return;
        }

        let mut mono_pgm = monomorph::monomorphise(&module, &opts.main);

        if opts.print_mono_ast {
            mono_ast::printer::print_pgm(&mono_pgm);
        }

        let lowered_pgm = lowering::lower(&mut mono_pgm);

        if opts.print_lowered_ast {
            lowering::printer::print_pgm(&lowered_pgm);
        }

        let mut w = std::io::stdout();
        program_args.insert(0, program);
        interpreter::run_with_args(&mut w, lowered_pgm, &opts.main, &program_args);
    }

    pub fn parse_file<P: AsRef<Path> + Clone>(
        path: P,
        module: &SmolStr,
        print_tokens: bool,
    ) -> ast::Module {
        let contents = std::fs::read_to_string(path.clone()).unwrap_or_else(|err| {
            panic!(
                "Unable to read file {} for module {}: {}",
                path.as_ref().to_string_lossy(),
                module,
                err
            )
        });
        let module_path: SmolStr = path.as_ref().to_string_lossy().into();
        parse_module(&module_path, &contents, print_tokens)
    }

    /// The `readFileUtf8` primitive.
    pub fn read_file_utf8(path: &str) -> String {
        std::fs::read_to_string(path).unwrap()
    }
}

use token::{Token, TokenKind};

fn combine_uppercase_lbrackets(tokens: Vec<(Loc, Token, Loc)>) -> Vec<(Loc, Token, Loc)> {
    let mut new_tokens = Vec::with_capacity(tokens.len());

    let mut iter = tokens.into_iter().peekable();
    while let Some((l, t, r)) = iter.next() {
        if let TokenKind::UpperId
        | TokenKind::UpperIdPath
        | TokenKind::TildeUpperId
        | TokenKind::TildeUpperIdPath = t.kind
        {
            if let Some((
                l_next,
                Token {
                    kind: TokenKind::LBracket,
                    text: _,
                },
                r_next,
            )) = iter.peek()
            {
                // TODO: This assumes 1-byte character, which holds today, but may not in the
                // future.
                if r.byte_idx == l_next.byte_idx {
                    let r_next = *r_next;
                    iter.next(); // consume '['
                    new_tokens.push((
                        l,
                        Token {
                            kind: match t.kind {
                                TokenKind::UpperId => TokenKind::UpperIdLBracket,
                                TokenKind::UpperIdPath => TokenKind::UpperIdPathLBracket,
                                TokenKind::TildeUpperId => TokenKind::TildeUpperIdLBracket,
                                TokenKind::TildeUpperIdPath => TokenKind::TildeUpperIdPathLBracket,
                                _ => panic!(),
                            },
                            text: t.text, // NB. Does not include the lbracket in text as parser needs the id text
                        },
                        r_next,
                    ));
                    continue;
                }
            }
        }

        new_tokens.push((l, t, r));
    }

    new_tokens
}

#[cfg(not(target_arch = "wasm32"))]
pub use native::{main, parse_file, read_file_utf8};

#[cfg(target_arch = "wasm32")]
mod wasm {
    use super::*;

    use std::io::Write;
    use std::path::Path;

    use smol_str::SmolStr;
    use wasm_bindgen::prelude::wasm_bindgen;

    pub fn parse_file<P: AsRef<Path> + Clone>(
        path: P,
        module: &SmolStr,
        _print_tokens: bool,
    ) -> ast::Module {
        let path = path.as_ref().to_string_lossy();
        let contents = read_file_utf8(&path);
        parse_module(&module, &contents, false)
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

        #[wasm_bindgen(js_name = "readFileUtf8")]
        pub fn read_file_utf8(path: &str) -> String;
    }

    #[wasm_bindgen(js_name = "setupPanicHook")]
    pub fn setup_panic_hook() {
        std::panic::set_hook(Box::new(hook_impl));
    }

    fn hook_impl(panic_info: &std::panic::PanicHookInfo) {
        if let Some(s) = panic_info.payload().downcast_ref::<String>() {
            add_interpreter_output(s);
        } else if let Some(s) = panic_info.payload().downcast_ref::<&str>() {
            add_interpreter_output(s);
        } else {
            add_interpreter_output("Weird panic payload in panic handler");
        }
    }

    #[wasm_bindgen(js_name = "run")]
    pub fn run_wasm(pgm: &str, mut args: Vec<String>) {
        args.insert(0, pgm.to_string());

        let module_name = SmolStr::new_static("FirWeb");
        let module = parse_module(&module_name, pgm, false);
        let mut import_path: crate::collections::Map<String, String> = Default::default();
        import_path.insert("Fir".to_string(), "fir/lib".to_string());
        let mut module = import_resolver::resolve_imports(&import_path, "", module, true, false);

        type_checker::check_module(&mut module, "fir/lib".to_string());

        let mut mono_pgm = monomorph::monomorphise(&module, "main");
        let lowered_pgm = lowering::lower(&mut mono_pgm);

        let mut w = WasmOutput;
        interpreter::run_with_args(&mut w, lowered_pgm, "main", &args);
    }

    #[wasm_bindgen(js_name = "version")]
    pub fn version() -> String {
        rustc_tools_util::get_version_info!().to_string()
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
pub use wasm::{parse_file, read_file_utf8};

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
        let tokens = scan(lex(pgm, "test").into_iter(), "test");
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
        let tokens = scan(lex(pgm, "test").into_iter(), "test");
        let ast = crate::parser::LStmtParser::new()
            .parse(&"".into(), tokens)
            .unwrap();
        dbg!(ast);
    }

    #[test]
    fn parse_fn_1() {
        let pgm = indoc::indoc! {"
            asdf():
                let q = match t():
                    A.X: 1
                q
        "};
        let tokens = scan(lex(pgm, "test").into_iter(), "test");
        let ast = crate::parser::TopDeclsParser::new()
            .parse(&"".into(), tokens)
            .unwrap();
        dbg!(ast);

        let pgm = indoc::indoc! {"
            asdf():
                let q = if A:
                    1
                else:
                    2
                q
        "};
        let tokens = scan(lex(pgm, "test").into_iter(), "test");
        let ast = crate::parser::TopDeclsParser::new()
            .parse(&"".into(), tokens)
            .unwrap();
        dbg!(ast);
    }
}
