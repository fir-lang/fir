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

    let parts: Vec[Str] = Vec.withCapacity(5)
    let startIdx: U32 = 0
    for i: U32 in range(u32(0), path.len()):
        if path.charAt(i) == '/':
            parts.push(path.substr(startIdx, i))
            startIdx = i + 1

    parts.push(path.substr(startIdx, path.len()))

    let pgm = Program.new()
    pgm.loadCachedModule(parts)
    pgm.prepModuleEnvs()
    resolveNames(pgm)

    match try(||: prepTcEnvs(pgm)):
        Result.Ok(()): ()
        Result.Err(err):
            print(err.toDoc().render(80))
            return

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
