import Scanner


type TestError:
    ParseError(ParseError[Token])
    Other(Str)


impl ToStr[TestError]:
    toStr(self: TestError) Str:
        match self:
            TestError.ParseError(parseError): parseError.toStr()
            TestError.Other(msg): msg


runParser(
        input: Str,
        parseFn: Fn(Vec[Token], U32) (tree: ParseTree[Token, nt], newCursor: U32) / ParseError[Token],
        runScan: Bool,
    ) ParseTree[Token, nt] / TestError:
    let (tokens, error) = tokenize("<test input>", input)

    if error is Option.Some(error):
        panic(lexerErrorStr(error))

    if runScan:
        tokens = match try(||: scan[row[]](tokens)):
            Result.Err(~ScannerError(line, col, msg)):
                throw(TestError.Other("scanner error: `line + 1`:`col + 1`: `msg`"))
            Result.Ok(tokens):
                tokens

    let result = match try(||: parseFn(tokens, 0)):
        Result.Err(err): throw(TestError.ParseError(err))
        Result.Ok(result): result

    if result.newCursor != tokens.len():
        throw(TestError.Other("parser didn't consume all input, input len = `tokens.len()`, cursor after parsing = `result.newCursor`"))

    result.tree


## Print test name, run the given parser function on the input, print errors and trees.
runTest[ToStr[nt]](
        testName: Str,
        input: Str,
        parseFn: Fn(Vec[Token], U32) (tree: ParseTree[Token, nt], newCursor: U32) / ParseError[Token],
    ) / exn:
    print(testName)
    match try(||: runParser(input, parseFn, Bool.False)):
        Result.Ok(tree): print(tree.toDoc().render(80))
        Result.Err(err): print("ERR: `err`")
    print("")


## Print input, run the given parser function on the input, print errors and trees.
##
## Difference from `runTest` is that this prints the input, `runTest` prints the given test name.
runTest_[ToStr[nt]](
        input: Str,
        parseFn: Fn(Vec[Token], U32) (tree: ParseTree[Token, nt], newCursor: U32) / ParseError[Token],
    ) / exn:
    print(input)
    match try(||: runParser(input, parseFn, Bool.False)):
        Result.Ok(tree): print(tree.toDoc().render(80))
        Result.Err(err): print("ERR: `err`")
    print("")


runTestIndent[ToStr[nt]](
        input: Str,
        parseFn: Fn(Vec[Token], U32) (tree: ParseTree[Token, nt], newCursor: U32) / ParseError[Token],
    ) Bool / exn:
    print(input)
    let result = match try(||: runParser(input, parseFn, Bool.True)):
        Result.Ok(tree):
            print(tree.toDoc().render(80))
            Bool.True
        Result.Err(err):
            print("ERR: `err`")
            Bool.False
    print("")
    result


lexerErrorStr(err: Error) Str:
    "`err.loc.file`:`err.loc.line + 1`:`err.loc.col + 1`: `err.msg`"
