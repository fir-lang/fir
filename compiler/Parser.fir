import Error
import Grammar
import Scanner

main(args: Array[Str]):
    if args.len() != 2:
        panic("USAGE: fir compiler/Parser.fir -- <file>")

    let file = args.get(1)
    let fileContents = readFileUtf8(file)

    let (tokens, error) = tokenize(file, fileContents)
    if error is Option.Some(error):
        print("ERROR: `error.loc.line + 1`:`error.loc.col + 1`: `error.msg`")

    let tokens = match try(||: scan[row[]](tokens)):    # Explicitly close the variant (issue #49).
        Result.Err(~ScannerError(line, col, msg)):
            panic("`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens):
            tokens

    let result = match try(||: module(tokens, 0)):
        Result.Err(ParseError(cursor)):
            if cursor == tokens.len():
                panic("Parse error: unexpected end of input")
            else:
                panic("Parse error: unexpected token `tokens.get(cursor)`")
        Result.Ok(result): result

    if result.newCursor != tokens.len():
        print("Parser didn't consume all input, input len = `tokens.len()`, cursor after parsing = `result.newCursor`")

    let buf = StrBuf.withCapacity(1_000_000)
    for topDecl: ParseTree[Token, NonTerminal] in result.tree.asNonTerminal(NonTerminal.Module).iter():
        topDecl.toDoc().renderToBuf(80, buf)
        print(buf.toStr())
        buf.clear()
