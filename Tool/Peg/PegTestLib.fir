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
    parseFn: Fn(ParserState[Token, ()]) tree / U32,
    runScan: Bool,
) tree / TestError:
    runParserState(input, parseFn, (), runScan)


runParserState(
    input: Str,
    parseFn: Fn(ParserState[Token, s]) tree / U32,
    state: s,
    runScan: Bool,
) tree / TestError:
    let (tokens, error) = tokenize("<test input>", input)

    if error is Option.Some(error):
        panic(error.toStr())

    let tokens = if runScan:
        match try(\(): scan[row[]](tokens)):
            Result.Err(~ScannerError(line, col, msg)):
                throw(
                    TestError.Other("scanner error: `line + 1`:`col + 1`: `msg`"),
                )
            Result.Ok(tokens): tokens.takeArray()
    else:
        tokens.takeArray()

    let parserState = ParserState.new(tokens, state)

    let tree = match try(\(): parseFn(parserState)):
        Result.Err(err): throw(TestError.ParseError(err))
        Result.Ok(tree): tree

    if not parserState.allConsumed():
        let numTokens = tokens.len()
        let cursor = parserState._cursor
        throw(
            TestError.Other(
                "parser didn't consume all input, input len = `numTokens`, cursor after parsing = `cursor`",
            ),
        )

    tree


## Print test name, run the given parser function on the input, print errors and trees.
runTest[ToDoc[pt]](
    testName: Str,
    input: Str,
    parseFn: Fn(ParserState[Token, ()]) pt / U32,
) / exn:
    runTestState(testName, input, parseFn, ())


runTestState[ToDoc[pt]](
    testName: Str,
    input: Str,
    parseFn: Fn(ParserState[Token, st]) pt / U32,
    state: st,
) / exn:
    print(testName)
    match try(\(): runParserState(input, parseFn, state, Bool.False)):
        Result.Ok(tree): print(tree.toDoc().render(80))
        Result.Err(err): print("ERR: `err`")
    print("")


## Print input, run the given parser function on the input, print errors and trees.
##
## Difference from `runTest` is that this prints the input, `runTest` prints the given test name.
runTest_[ToStr[nt]](
    input: Str,
    parseFn: Fn(ParserState[Token, ()]) ParseTree[Token, nt] / U32,
) / exn:
    print(input)
    match try(\(): runParser(input, parseFn, Bool.False)):
        Result.Ok(tree): print(tree.toDoc().render(80))
        Result.Err(err): print("ERR: `err`")
    print("")


## Same as `runTest_`, but runs scanner after lexer.
runTestScanner_[ToStr[nt]](
    input: Str,
    parseFn: Fn(ParserState[Token, ()]) ParseTree[Token, nt] / U32,
) / exn:
    print(input)
    match try(\(): runParser(input, parseFn, Bool.True)):
        Result.Ok(tree): print(tree.toDoc().render(80))
        Result.Err(err): print("ERR: `err`")
    print("")


runTestIndent[ToStr[nt]](
    input: Str,
    parseFn: Fn(ParserState[Token, ()]) ParseTree[Token, nt] / U32,
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
