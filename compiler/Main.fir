import Ast
import AstPrinter
import Lexer

main(args: Array[Str])
    let filePath = args.get(1)
    let fileContents = readFileUtf8(filePath)
    let (tokens, error) = tokenize(filePath, fileContents)
    for token: Token in tokens.iter():
        print(token)
    if error is Option.Some(error):
        printStr("ERROR: `error.loc.byteIdx`: `error.msg`")

assertEq[Eq[t], ToStr[t]](expected: t, found: t): [AssertionError(msg: Str), ..r] ()
    if expected != found:
        throw(~AssertionError(msg = "Expected `expected`, found `found`"))
