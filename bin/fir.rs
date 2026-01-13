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
                .help("Don't implicitly import Fir.Prelude."),
        )
        .arg(
            clap::Arg::new(BACKTRACE)
                .long(BACKTRACE)
                .num_args(0)
                .help("Print interpreter backtraces in pacnis."),
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
            clap::Arg::new(PROGRAM_ARGS)
                .last(true)
                .allow_hyphen_values(true)
                .num_args(0..),
        )
        .arg(
            clap::Arg::new(TO_C)
                .long(TO_C)
                .num_args(0)
                .help("Compile to C"),
        )
        .get_matches();

    let compiler_opts = fir::CompilerOpts {
        typecheck: matches.get_flag(TYPECHECK),
        no_prelude: matches.get_flag(NO_PRELUDE),
        backtrace: matches.get_flag(BACKTRACE),
        tokenize: matches.get_flag(TOKENIZE),
        scan: matches.get_flag(SCAN),
        print_parsed_ast: matches.get_flag(PRINT_PARSED_AST),
        print_checked_ast: matches.get_flag(PRINT_CHECKED_AST),
        print_mono_ast: matches.get_flag(PRINT_MONO_AST),
        print_lowered_ast: matches.get_flag(PRINT_LOWERED_AST),
        main: matches.get_one(MAIN).cloned().unwrap(),
        to_c: matches.get_flag(TO_C),
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
const BACKTRACE: &str = "backtrace";
const TOKENIZE: &str = "tokenize";
const SCAN: &str = "scan";
const PRINT_PARSED_AST: &str = "print-parsed-ast";
const PRINT_CHECKED_AST: &str = "print-checked-ast";
const PRINT_MONO_AST: &str = "print-mono-ast";
const PRINT_LOWERED_AST: &str = "print-lowered-ast";
const MAIN: &str = "main";
const PROGRAM: &str = "program";
const PROGRAM_ARGS: &str = "program-args";
const TO_C: &str = "to-c";

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
