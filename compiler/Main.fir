import Ast
import AstPrinter
import Lexer
import Parser
import Scanner

main(args: Array[Str])
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

    print("")
    print("PARSER TESTS")
    print("")
    parserTests()

    print("")
    print("PRINTER TESTS")
    print("")

    print(parseExpr("1 + 2").pprint().print(80))
    print(parseExpr("1 + 2 + 3").pprint().print(80))
    print(parseExpr("1 * 2 + 3").pprint().print(80))
    print(parseExpr("1 + 2 * 3").pprint().print(80))
    print(parseExpr("1 * 2 * 3").pprint().print(80))

parseExpr(input: Str): Expr
    let (tokens, error) = tokenize("Test.fir", input)
    if error is Option.Some(err):
        panic("\t\tLexer error: `err.msg`")

    let parser = Parser(_file = "Test.fir", _tokens = tokens, _idx = 0)
    match try({ parser.expr(0) }):
        Result.Err(err):
            panic("\t\tParser error: `err.msg`")
        Result.Ok(ast):
            ast.node

assertEq[Eq[t], ToStr[t]](expected: t, found: t): [AssertionError(msg: Str), ..r] ()
    if expected != found:
        throw(~AssertionError(msg = "Expected `expected`, found `found`"))
