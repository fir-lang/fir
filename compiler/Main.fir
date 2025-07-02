import Ast
import AstPrinter
import Lexer
import Scanner

main(args: Array[Str]):
    if args.len() >= 2:
        let filePath = args.get(1)
        let fileContents = readFileUtf8(filePath)
        let (tokens, error) = tokenize(filePath, fileContents)
        tokens = scan(tokens)
        for token: Token in tokens.iter():
            print(token)
        if error is Option.Some(error):
            printStr("ERROR: `error.loc.byteIdx`: `error.msg`")
        return

    print("SCANNER TESTS")
    print("")
    scannerTests()

assertEq[Eq[t], ToStr[t]](expected: t, found: t) () / [AssertionError, ..r]:
    if expected != found:
        throw(~AssertionError(msg = "Expected `expected`, found `found`"))
