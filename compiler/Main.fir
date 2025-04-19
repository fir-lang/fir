import Ast
import Lexer

main(args: Array[Str])
    let filePath = args.get(1)
    let fileContents = readFileUtf8(filePath)
    let (tokens = tokens, error = error) = tokenize(filePath, fileContents)
    for token: Token in tokens.iter():
        printStr(token.toStr())
    match error:
        Option.Some(error): printStr("ERROR: `error.loc.byteIdx.toStr()`: `error.msg`")
        Option.None: ()
