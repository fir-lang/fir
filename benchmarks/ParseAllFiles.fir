import [
    Compiler/Ast2,
    Compiler/Error,
    Compiler/Grammar2,
    Compiler/Scanner,
]


main():
    for file in getArgs().iter().skip(1):
        parse(file)


parse(modulePath: Str):
    print(modulePath)

    let moduleContents = readFileUtf8(modulePath)

    let (tokens, error) = tokenize(modulePath, moduleContents)
    if error is Option.Some(error):
        panic("ERROR: `error.loc.line + 1`:`error.loc.col + 1`: `error.msg`")

    # Explicitly close the variant with `row[]` (issue #49).
    let tokens = match try(\(): scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens): tokens.takeArray()

    let parserState = ParserState.new(tokens, ())

    let tree: Vec[TopDecl[DefaultAstExts]] = match try(\(): module(parserState)):
        Result.Err(cursor):
            if cursor == tokens.len():
                panic("Parse error: unexpected end of input")
            else:
                panic("Parse error: unexpected token `tokens.get(cursor)`")
        Result.Ok(tree): tree

    ()
