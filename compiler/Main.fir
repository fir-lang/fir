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

assertEq[Eq[t], ToStr[t]](val1: t, val2: t)
    if val1 != val2:
        panic("Expected `val1`, found `val2`")

parserTests
    parserTest("A", Parser.simpleExpr, fn(ast) {
        match ast:
            Expr.Constr(constr):
                assertEq(constr.id.name, "A")
            _:
                panic("Expected constr")
    })
