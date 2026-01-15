use fir::cli::*;

fn main() {
    let FirArgs {
        opts,
        program,
        program_args,
    } = get_fir_args(Mode::ToC);
    fir::main(opts, program, program_args)
}
