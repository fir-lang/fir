use fir::cli::*;

fn main() {
    let FirArgs {
        opts,
        program,
        program_args,
    } = get_fir_args();
    fir::main(opts, program, program_args)
}
