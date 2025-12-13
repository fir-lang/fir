import [
    Compiler/Error,
    Compiler/Grammar,
    Compiler/Scanner,
]


main():
    let args = getArgs()

    let printAst = Bool.False
    let path: Option[Str] = Option.None

    for arg: Str in args.iter().skip(1):
        if arg == "--print":
            printAst = Bool.True
        else:
            if path is Option.Some(_):
                showUsageAndExit()

            path = Option.Some(arg)

    let path = path.unwrapOrElse(showUsageAndExit)
    let fileContents = readFileUtf8(path)

    let (tokens, error) = tokenize(path, fileContents)
    if error is Option.Some(error):
        print("ERROR: `error`")

    # Explicitly close the variant with `row[]`. (#49)
    let tokens = match try(\(): scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens): tokens.takeArray()

    let mod = match try(\(): module(ParserState.new(tokens))):
        Result.Err(cursor):
            if cursor == tokens.len():
                panic("Parse error: unexpected end of input")
            else:
                panic("Parse error: unexpected token `tokens.get(cursor)`")
        Result.Ok(mod): mod

    if printAst:
        for decl: TopDecl in mod.iter():
            print(decl.toDoc().render(80))
            print("")


showUsageAndExit() a:
    panic("USAGE: fir Compiler/Parser.fir -- <file> [--print]")
