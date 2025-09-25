import [
    Compiler/Ast,
    Compiler/AstWalker,
    Compiler/NameResolver,
    Compiler/Program,
]


main():
    let args = getArgs()

    if args.len() != 2:
        panic("USAGE: fir Tool/Merge/Merge.fir -- <path>")

    let path = args.get(1)

    if not path.endsWith(".fir"):
        panic("File extension should be .fir")

    let pathNoExt = path.substr(0, path.len() - ".fir".len())

    let pathParts: Vec[Str] = Vec.withCapacity(5)
    let startIdx: U32 = 0
    for i: U32 in range(u32(0), pathNoExt.len()):
        if pathNoExt.charAt(i) == '/':
            pathParts.push(pathNoExt.substr(startIdx, i))
            startIdx = i + 1

    pathParts.push(pathNoExt.substr(startIdx, pathNoExt.len()))

    # Parse the program, load dependencies, resolve names.
    let pgm = Program.new()
    pgm.loadCachedModule(pathParts)
    pgm.prepModuleEnvs()
    resolveNames(pgm)

    # Find parsed main function, collect all definitions reachable from the main
    # function.

