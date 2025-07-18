fn main() {
    let matches = clap::Command::new("fir")
        .version(version_info_str(rustc_tools_util::get_version_info!()))
        .arg(
            clap::Arg::new(TYPECHECK)
                .long(TYPECHECK)
                .num_args(0)
                .help("Don't run the program, only type check."),
        )
        .arg(
            clap::Arg::new(NO_PRELUDE)
                .long(NO_PRELUDE)
                .num_args(0)
                .help("Don't implicitly import Prelude."),
        )
        .arg(
            clap::Arg::new(NO_BACKTRACE)
                .long(NO_BACKTRACE)
                .num_args(0)
                .help("Don't print backtraces in panics."),
        )
        .arg(
            clap::Arg::new(TOKENIZE)
                .long(TOKENIZE)
                .num_args(0)
                .help("Print tokens and stop."),
        )
        .arg(
            clap::Arg::new(SCAN)
                .long(SCAN)
                .num_args(0)
                .help("Print scanned tokens and stop."),
        )
        .arg(
            clap::Arg::new(PRINT_PARSED_AST)
                .long(PRINT_PARSED_AST)
                .num_args(0)
                .help("Print AST after parsing."),
        )
        .arg(
            clap::Arg::new(PRINT_CHECKED_AST)
                .long(PRINT_CHECKED_AST)
                .num_args(0)
                .help("Print AST after type checking."),
        )
        .arg(
            clap::Arg::new(PRINT_MONO_AST)
                .long(PRINT_MONO_AST)
                .num_args(0)
                .help("Print AST after monomorphisation."),
        )
        .arg(
            clap::Arg::new(PRINT_LOWERED_AST)
                .long(PRINT_LOWERED_AST)
                .num_args(0)
                .help("Print AST after lowering."),
        )
        .arg(
            clap::Arg::new(MAIN)
                .long(MAIN)
                .num_args(1)
                .required(false)
                .default_value("main")
                .help("Name of the main function to run."),
        )
        .arg(
            clap::Arg::new(PROGRAM)
                .num_args(1)
                .required(true)
                .help("Path to the program to run."),
        )
        .arg(
            clap::Arg::new(IMPORT_PATH)
                .long(IMPORT_PATH)
                .short('i')
                .action(clap::ArgAction::Append)
                .help("<module name>=<file path> pairs for resolving imports")
                .value_parser(parse_key_val),
        )
        .arg(
            clap::Arg::new(PROGRAM_ARGS)
                .last(true)
                .allow_hyphen_values(true)
                .num_args(0..),
        )
        .get_matches();

    let compiler_opts = fir::CompilerOpts {
        typecheck: matches.get_flag(TYPECHECK),
        no_prelude: matches.get_flag(NO_PRELUDE),
        no_backtrace: matches.get_flag(NO_BACKTRACE),
        tokenize: matches.get_flag(TOKENIZE),
        scan: matches.get_flag(SCAN),
        print_parsed_ast: matches.get_flag(PRINT_PARSED_AST),
        print_checked_ast: matches.get_flag(PRINT_CHECKED_AST),
        print_mono_ast: matches.get_flag(PRINT_MONO_AST),
        print_lowered_ast: matches.get_flag(PRINT_LOWERED_AST),
        main: matches.get_one(MAIN).cloned().unwrap(),
        import_paths: matches
            .get_many::<(String, String)>(IMPORT_PATH)
            .map(|pairs| pairs.map(|(k, v)| (k.clone(), v.clone())).collect())
            .unwrap_or_default(),
    };

    let program: String = matches.get_one::<String>(PROGRAM).unwrap().clone();

    let program_args: Vec<String> = match matches.get_many::<String>(PROGRAM_ARGS) {
        Some(args) => args.cloned().collect(),
        None => vec![],
    };

    fir::main(compiler_opts, program, program_args)
}

const TYPECHECK: &str = "typecheck";
const NO_PRELUDE: &str = "no-prelude";
const NO_BACKTRACE: &str = "no-backtrace";
const TOKENIZE: &str = "tokenize";
const SCAN: &str = "scan";
const PRINT_PARSED_AST: &str = "print-parsed-ast";
const PRINT_CHECKED_AST: &str = "print-checked-ast";
const PRINT_MONO_AST: &str = "print-mono-ast";
const PRINT_LOWERED_AST: &str = "print-lowered-ast";
const MAIN: &str = "main";
const PROGRAM: &str = "program";
const PROGRAM_ARGS: &str = "program-args";
const IMPORT_PATH: &str = "import-path";

// This is the same as `VersionInfo`'s `Display`, except it doesn't show the crate name as clap adds
// command name as prefix in `--version`.
fn version_info_str(version_info: rustc_tools_util::VersionInfo) -> String {
    let hash = version_info.commit_hash.clone().unwrap_or_default();
    let hash_trimmed = hash.trim();

    let date = version_info.commit_date.clone().unwrap_or_default();
    let date_trimmed = date.trim();

    if (hash_trimmed.len() + date_trimmed.len()) > 0 {
        format!(
            "{}.{}.{} ({hash_trimmed} {date_trimmed})",
            version_info.major, version_info.minor, version_info.patch,
        )
    } else {
        format!(
            "{}.{}.{}",
            version_info.major, version_info.minor, version_info.patch
        )
    }
}

fn parse_key_val(s: &str) -> Result<(String, String), String> {
    let parts: Vec<&str> = s.splitn(2, '=').collect();
    if parts.len() != 2 {
        return Err(format!("invalid key=value: `{s}`"));
    }
    Ok((parts[0].to_string(), parts[1].to_string()))
}
