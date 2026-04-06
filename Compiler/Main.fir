import [
    Compiler/NameResolver,
    Compiler/Program,
    Compiler/TypeCheck,
]


main():
    let args = getArgs()

    if args.len() == 1:
        return

    if args.len() != 2:
        panic("USAGE: fir Compiler/Main.fir -- <path>")

    let path = args.get(1)

    if not path.endsWith(".fir"):
        panic("File extension should be .fir")

    let path = path.substr(0, path.len() - ".fir".len())

    let parts: Vec[Str] = Vec.fromIter(path.splitChar('/'))

    let pgm = Program.new()
    pgm.loadCachedModule(parts)
    resolveNames(pgm)

    match try(\(): prepTcEnvs(pgm)):
        Result.Ok(()): ()
        Result.Err(err): panic(err.toDoc().render(80))

    # This prints too much stuff, commented out for now.
    # for mod: Module in pgm._modules.iter():
    #     print("`mod._filePath` tc env:")
    #     let tcEnvDoc = mod._tcEnv.unwrap().toDoc()
    #     let msgDoc = Doc.nested(
    #         4,
    #         Doc.str("`mod._filePath` tc env:") + Doc.hardLine() + tcEnvDoc,
    #     )
    #     print(msgDoc.render(200))
    ()
