#![allow(
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::large_enum_variant,
    unused_braces // lalrpop generates these
)]

mod ast;
pub mod cli;
mod collections;
mod deriving;
mod interpolation;
mod interpreter;
mod lexer;
mod lowering;
mod module;
mod module_loader;
mod mono_ast;
mod monomorph;
mod name;
mod parser;
mod parser_utils;
mod scanner;
mod scope_map;
mod to_c;
mod token;
mod type_checker;
mod type_collector;
mod utils;

use lexgen_util::Loc;
use smol_str::SmolStr;

#[derive(Debug, Clone)]
pub struct CompilerOpts {
    /// Stop after parsing.
    pub parse: bool,

    /// Stop after type checking.
    pub typecheck: bool,

    pub backtrace: bool,

    /// Print tokens and stop.
    pub tokenize: bool,

    /// Print scanned tokens and stop.
    pub scan: bool,

    pub print_parsed_ast: bool,
    pub print_expanded_ast: bool,
    pub print_checked_ast: bool,
    pub print_mono_ast: bool,
    pub print_lowered_ast: bool,
    pub main: String,
    pub to_c: bool,
    pub run_c: bool,
}

fn lexgen_loc_display(module: &SmolStr, lexgen_loc: lexgen_util::Loc) -> String {
    format!("{}:{}:{}", module, lexgen_loc.line + 1, lexgen_loc.col + 1)
}

fn parse_module(module: &SmolStr, contents: &str) -> ast::Module {
    let tokens = combine_uppercase_lbrackets(scanner::scan(
        lexer::lex(contents, module).into_iter(),
        module,
    ));
    // dbg!(tokens.iter().map(|(_, t, _)| t.clone()).collect::<Vec<_>>());

    let parser = parser::ModuleParser::new();
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
            panic!("Lexer error: {error:?}")
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
mod native {
    use super::*;

    use smol_str::SmolStr;
    use std::io::Write;
    use std::path::Path;

    pub fn main(opts: CompilerOpts, program: String, mut program_args: Vec<String>) {
        if opts.tokenize {
            let file_contents = std::fs::read_to_string(program).unwrap();
            for (l, t, _) in crate::lexer::lex(&file_contents, "test") {
                println!("{}:{}: {:?}", l.line + 1, l.col + 1, t.kind);
            }
            return;
        }

        if opts.scan {
            let file_contents = std::fs::read_to_string(program).unwrap();
            for (l, t, _) in scanner::scan(
                crate::lexer::lex(&file_contents, "test").into_iter(),
                "test",
            ) {
                println!("{}:{}: {:?}", l.line + 1, l.col + 1, t.kind);
            }
            return;
        }

        if !opts.backtrace {
            std::panic::set_hook(Box::new(|panic_info| {
                if let Some(s) = panic_info.payload().downcast_ref::<String>() {
                    eprintln!("{s}");
                } else if let Some(s) = panic_info.payload().downcast_ref::<&str>() {
                    eprintln!("{s}");
                } else {
                    eprintln!("Weird panic payload in panic handler");
                }
            }));
        }

        let file_path = Path::new(&program); // "examples/Foo.fir"
        let mut loaded_pgm = module_loader::load(file_path, opts.print_parsed_ast);

        if opts.parse {
            return;
        }

        deriving::expand_derives(&mut loaded_pgm);

        if opts.print_expanded_ast {
            loaded_pgm.print();
        }

        let (tys, module_envs) = type_checker::check_pgm(&mut loaded_pgm, &opts.main);

        if opts.print_checked_ast {
            loaded_pgm.print();
        }

        if opts.typecheck {
            return;
        }

        type_checker::check_main_type(&tys, &Default::default(), &loaded_pgm.entry, &opts.main);

        type_checker::expand_type_synonyms(&mut loaded_pgm);

        let mut mono_pgm = monomorph::monomorphise(&loaded_pgm, module_envs, &opts.main);

        if opts.print_mono_ast {
            mono_ast::printer::print_pgm(&mono_pgm);
        }

        let lowered_pgm = lowering::lower(&mut mono_pgm);

        if opts.print_lowered_ast {
            lowering::printer::print_pgm(&lowered_pgm);
        }

        if opts.run_c {
            let c = to_c::to_c(&lowered_pgm, &opts.main);
            let mut file = tempfile::NamedTempFile::with_suffix(".c").unwrap();
            let out_file_path = file.path().as_os_str().to_string_lossy().into_owned();
            let out_file_path = &out_file_path[..out_file_path.len() - 2];
            file.disable_cleanup(true);
            file.write_all(c.as_bytes()).unwrap();
            let mut gcc_cmd = std::process::Command::new("gcc");
            gcc_cmd
                .arg(file.path().as_os_str())
                .arg("-o")
                .arg(out_file_path)
                .arg("-Wall")
                .arg("-Wextra")
                .arg("-Wno-unused-variable")
                .arg("-Wno-unused-function")
                .arg("-Wno-unused-but-set-variable")
                .arg("-Wno-unused-value")
                .arg("-Wno-unused-parameter")
                .arg("-Wno-unused-label")
                .arg("-Wno-infinite-recursion");
            // dbg!(&gcc_cmd);
            let output = gcc_cmd.output().unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            if !output.status.success() {
                eprintln!("C compilation failed:");
            }
            if !stdout.is_empty() {
                eprintln!("stdout:");
                eprintln!("{}", String::from_utf8_lossy(&output.stdout));
            }
            if !stderr.is_empty() {
                eprintln!("stderr:");
                eprintln!("{}", String::from_utf8_lossy(&output.stderr));
            }
            if !output.status.success() {
                std::process::exit(1);
            }
            // dbg!(&out_file_path);
            // dbg!(&program_args);
            let status = std::process::Command::new(out_file_path)
                .args(program_args)
                .spawn()
                .unwrap()
                .wait()
                .unwrap();
            if !status.success() {
                std::process::exit(1);
            }
        } else if opts.to_c {
            println!("{}", to_c::to_c(&lowered_pgm, &opts.main));
        } else {
            let mut w = std::io::stdout();
            program_args.insert(0, program);
            interpreter::run_with_args(&mut w, lowered_pgm, &opts.main, program_args);
        }
    }

    pub fn parse_file<P: AsRef<Path> + Clone>(
        path: P,
        module: &str,
        print_parsed_ast: bool,
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
        let parsed = parse_module(&module_path, &contents);
        if print_parsed_ast {
            println!("mod {} {{\n", module);
            parsed.print();
            println!("\n}} # {}\n", module);
        }
        parsed
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
        if let TokenKind::UpperId | TokenKind::UpperIdPath = t.kind
            && let Some((
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
                            _ => panic!(),
                        },
                        text: t.text, // NB. Does not include the lbracket in text as parser needs the id text
                    },
                    r_next,
                ));
                continue;
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
        module: &str,
        _print_parsed_ast: bool,
    ) -> ast::Module {
        let path = path.as_ref().to_string_lossy();
        let contents = read_file_utf8(&path);
        let module_path: SmolStr = path.into();
        parse_module(&module_path, &contents)
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

        // NB. This path handled specially in the web page, it returns the program input field
        // contents.
        let file_path = Path::new("Main.fir");
        let mut loaded_program = module_loader::load(file_path, false);
        deriving::expand_derives(&mut loaded_program);

        let (_tys, module_envs) = type_checker::check_pgm(&mut loaded_program, "main");

        type_checker::expand_type_synonyms(&mut loaded_program);
        let mut mono_pgm = monomorph::monomorphise(&loaded_program, module_envs, "main");
        let lowered_pgm = lowering::lower(&mut mono_pgm);

        let mut w = WasmOutput;
        interpreter::run_with_args(&mut w, lowered_pgm, "main", args);
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
        let ast = crate::parser::ModuleParser::new()
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
        let ast = crate::parser::ModuleParser::new()
            .parse(&"".into(), tokens)
            .unwrap();
        dbg!(ast);
    }

    #[test]
    fn parse_imports() {
        use crate::ast::{ImportSpec, TopDecl};
        use crate::module::ModulePath;

        use smol_str::SmolStr;

        let pgm = indoc::indoc! {"
            import [
                A,
                A/[f1, f2],
                A/B/C,
                A/B/D as E,
                A as B,
                A/B/D/[f1, f2, Type1, Type2],
                A/B/D/[f1 as g1, f2, Type1 as MyType, Type2],
                A/B/D/[f1 as _f1, Type1 as _Type1],
            ]
        "};
        let tokens = scan(lex(pgm, "test").into_iter(), "test");
        let module = crate::parser::ModuleParser::new()
            .parse(&"test".into(), tokens)
            .unwrap();
        assert_eq!(module.decls.len(), 1);
        let import = match &module.decls[0].node {
            TopDecl::Import(i) => &i.node,
            other => panic!("expected import, got {:?}", other),
        };
        assert_eq!(import.items.len(), 8);

        // 0: A (import everything)
        assert_eq!(
            import.items[0].path,
            ModulePath::new(vec![SmolStr::new_static("A")]),
        );
        assert_eq!(import.items[0].import_spec, None);

        // 1: A/[f1, f2]
        assert_eq!(
            import.items[1].path,
            ModulePath::new(vec![SmolStr::new_static("A")]),
        );
        match &import.items[1].import_spec {
            Some(ImportSpec::Selective { names }) => {
                assert_eq!(names.len(), 2);
                assert_eq!(names[0].original_name, "f1");
                assert_eq!(names[1].original_name, "f2");
            }
            other => panic!("expected Selective, got {:?}", other),
        }

        // 2: A/B/C (import everything)
        assert_eq!(
            import.items[2].path,
            ModulePath::new(vec![
                SmolStr::new_static("A"),
                SmolStr::new_static("B"),
                SmolStr::new_static("C")
            ])
        );
        assert_eq!(import.items[2].import_spec, None);

        // 3: A/B/D as E
        assert_eq!(
            import.items[3].path,
            ModulePath::new(vec![
                SmolStr::new_static("A"),
                SmolStr::new_static("B"),
                SmolStr::new_static("D")
            ])
        );
        match &import.items[3].import_spec {
            Some(ImportSpec::Prefixed { prefix }) => assert_eq!(prefix, "E"),
            other => panic!("expected Prefixed, got {:?}", other),
        }

        // 4: A as B
        assert_eq!(
            import.items[4].path,
            ModulePath::new(vec![SmolStr::new_static("A")]),
        );
        match &import.items[4].import_spec {
            Some(ImportSpec::Prefixed { prefix }) => assert_eq!(prefix, "B"),
            other => panic!("expected Prefixed, got {:?}", other),
        }

        // 5: A/B/D/[f1, f2, Type1, Type2]
        assert_eq!(
            import.items[5].path,
            ModulePath::new(vec![
                SmolStr::new_static("A"),
                SmolStr::new_static("B"),
                SmolStr::new_static("D")
            ])
        );
        match &import.items[5].import_spec {
            Some(ImportSpec::Selective { names }) => {
                assert_eq!(names.len(), 4);
                assert_eq!(names[0].original_name, "f1");
                assert_eq!(names[0].local_name, "f1");
                assert_eq!(names[2].original_name, "Type1");
            }
            other => panic!("expected Selective, got {:?}", other),
        }

        // 6: A/B/D/[f1 as g1, f2, Type1 as MyType, Type2]
        match &import.items[6].import_spec {
            Some(ImportSpec::Selective { names }) => {
                assert_eq!(names[0].original_name, "f1");
                assert_eq!(names[0].local_name, "g1");
                assert_eq!(names[1].original_name, "f2");
                assert_eq!(names[1].local_name, "f2");
                assert_eq!(names[2].original_name, "Type1");
                assert_eq!(names[2].local_name, "MyType");
            }
            other => panic!("expected Selective, got {:?}", other),
        }

        // 7: A/B/D/[f1 as _f1, Type1 as _Type1]
        match &import.items[7].import_spec {
            Some(ImportSpec::Selective { names }) => {
                assert_eq!(names[0].local_name, "_f1");
                assert_eq!(names[1].local_name, "_Type1");
            }
            other => panic!("expected Selective, got {:?}", other),
        }
    }
}
