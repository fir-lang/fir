import [Compiler/Scanner]


type TestError:
    ParseError(U32)
    Other(Str)


impl ToStr[TestError]:
    toStr(self: TestError) Str:
        match self:
            TestError.ParseError(errCur):
                "unexpected token or end of input at cursor `errCur`"
            TestError.Other(msg): msg


runParser(
    input: Str,
    parseFn: Fn(ParserState[Token]) tree / U32,
    runScan: Bool,
) tree / TestError:
    let (tokens, error) = tokenize("<test input>", input)

    if error is Option.Some(error):
        panic(error.toStr())

    if runScan:
        tokens = match try(\(): scan[row[]](tokens)):
            Result.Err(~ScannerError(line, col, msg)):
                throw(
                    TestError.Other("scanner error: `line + 1`:`col + 1`: `msg`"),
                )
            Result.Ok(tokens): tokens

    let parserState = ParserState.new(tokens)

    let tree = match try(\(): parseFn(parserState)):
        Result.Err(err): throw(TestError.ParseError(err))
        Result.Ok(tree): tree

    if not parserState.allConsumed():
        throw(
            TestError.Other(
                "parser didn't consume all input, input len = `tokens.len()`, cursor after parsing = `parserState._cursor`",
            ),
        )

    tree


## Print test name, run the given parser function on the input, print errors and trees.
runTest[ToStr[nt]](
    testName: Str,
    input: Str,
    parseFn: Fn(ParserState[Token]) ParseTree[Token, nt] / U32,
) / exn:
    print(testName)
    match try(\(): runParser(input, parseFn, Bool.False)):
        Result.Ok(tree): print(tree.toDoc().render(80))
        Result.Err(err): print("ERR: `err`")
    print("")


## Print input, run the given parser function on the input, print errors and trees.
##
## Difference from `runTest` is that this prints the input, `runTest` prints the given test name.
runTest_[ToStr[nt]](
    input: Str,
    parseFn: Fn(ParserState[Token]) ParseTree[Token, nt] / U32,
) / exn:
    print(input)
    match try(\(): runParser(input, parseFn, Bool.False)):
        Result.Ok(tree): print(tree.toDoc().render(80))
        Result.Err(err): print("ERR: `err`")
    print("")


## Same as `runTest_`, but runs scanner after lexer.
runTestScanner_[ToStr[nt]](
    input: Str,
    parseFn: Fn(ParserState[Token]) ParseTree[Token, nt] / U32,
) / exn:
    print(input)
    match try(\(): runParser(input, parseFn, Bool.True)):
        Result.Ok(tree): print(tree.toDoc().render(80))
        Result.Err(err): print("ERR: `err`")
    print("")


runTestIndent[ToStr[nt]](
    input: Str,
    parseFn: Fn(ParserState[Token]) ParseTree[Token, nt] / U32,
) Bool / exn:
    print(input)
    let result = match try(\(): runParser(input, parseFn, Bool.True)):
        Result.Ok(tree):
            print(tree.toDoc().render(80))
            Bool.True
        Result.Err(err):
            print("ERR: `err`")
            Bool.False
    print("")
    result
