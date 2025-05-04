import Ast
import AstPrinter
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

    print("")
    print("PRINTER TESTS")
    print("")

    _parserTest(
        "pprint BinOp",
        "1 + 2 + 3",
        fn(s) { Parser.expr(s,0) },
        fn(expr) { print(expr.node.pprint().print(40)) },
    )

assertEq[Eq[t], ToStr[t]](expected: t, found: t): [AssertionError(msg: Str), ..r] ()
    if expected != found:
        throw(~AssertionError(msg = "Expected `expected`, found `found`"))
