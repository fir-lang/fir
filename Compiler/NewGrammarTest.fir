import [
    Compiler/Ast,
    Compiler/Grammar,
    Compiler/Lexer,
    Compiler/Scanner,
]


main():
    let args = getArgs()

    if args.len() == 1:
        return

    let path = args.get(1)

    if not path.endsWith(".fir"):
        panic("File extension should be .fir")

    let fileContents = readFileUtf8(path)

    let (tokens, error) = tokenize(path, fileContents)
    if error is Option.Some(error):
        panic("`path`:`error.loc.line + 1`:`error.loc.col + 1`: `error.msg`")

    # Explicitly close the variant with `row[]`. (#49)
    let tokens = match try(\(): scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("`path`:`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens): tokens.takeArray()

    let result: Result[U32, Vec[TopDecl[DefaultAstExts]]] = try(
        \(): module(ParserState.new(tokens, ()))
    )

    match result:
        Result.Err(cursor):
            match tokens.getOpt(cursor):
                Option.None: panic("`path`: unexpected end of input")
                Option.Some(token):
                    panic(
                        "`path`:`token.line + 1`:`token.col + 1`: unexpected token `token`",
                    )
        Result.Ok(parsed): print(parsed.toDoc().render(80))
