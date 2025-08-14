import Error
import Grammar
import Scanner

main(args: Array[Str]):
    let printAst = Bool.False
    let path: Option[Str] = Option.None

    for arg: Str in args.iter().skip(1):
        if arg == "--print":
            printAst = Bool.True
        else:
            if path.isSome():
                showUsageAndExit()

            path = Option.Some(arg)

    let path = path.unwrapOrElse(showUsageAndExit)
    let fileContents = readFileUtf8(path)

    let (tokens, error) = tokenize(path, fileContents)
    if error is Option.Some(error):
        print("ERROR: `error.loc.line + 1`:`error.loc.col + 1`: `error.msg`")

    let tokens = match try(||: scan[row[]](tokens)):    # Explicitly close the variant (issue #49).
        Result.Err(~ScannerError(line, col, msg)):
            panic("`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens):
            tokens

    let parserState = ParserState.new(tokens)

    let tree = match try(||: module(parserState)):
        Result.Err(cursor):
            if cursor == tokens.len():
                panic("Parse error: unexpected end of input")
            else:
                panic("Parse error: unexpected token `tokens.get(cursor)`")
        Result.Ok(tree): tree

    if not parserState.allConsumed():
        print("Parser didn't consume all input, input len = `tokens.len()`, cursor after parsing = `parserState._cursor`")

    # if printAst:
    #     let buf = StrBuf.withCapacity(1_000_000)
    #     for topDecl: ParseTree[Token, NonTerminal] in result.tree.asNonTerminal(NonTerminal.Module).iter():
    #         topDecl.toDoc().renderToBuf(80, buf)
    #         print(buf.toStr())
    #         buf.clear()

showUsageAndExit() a:
    panic("USAGE: fir compiler/Parser.fir -- <file> [--print]")
