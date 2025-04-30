import Ast
import Lexer
import Parser

main(args: Array[Str])
    let filePath = args.get(1)
    let fileContents = readFileUtf8(filePath)
    let (tokens = tokens, error = error) = tokenize(filePath, fileContents)
    for token: Token in tokens.iter():
        print(token)
    match error:
        Option.Some(error): printStr("ERROR: `error.loc.byteIdx`: `error.msg`")
        Option.None: ()

    print("")
    print("PARSER TESTS")
    print("")
    parserTests()

assertEq[Eq[t], ToStr[t]](expected: t, found: t): [AssertionError(msg: Str), ..r] ()
    if expected != found:
        throw(~AssertionError(msg = "Expected `expected`, found `found`"))
