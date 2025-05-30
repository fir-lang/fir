type TestError:
    ParseError(ParseError[Token])
    Other(Str)

impl ToStr[TestError]:
    toStr(self: TestError): Str
        match self:
            TestError.ParseError(parseError): parseError.toStr()
            TestError.Other(msg): msg

runParser(
        input: Str,
        parseFn: Fn(Vec[Token], U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    ): TestError ParseTree[Token, NonTerminal]
    let (tokens, error) = tokenize("<test input>", input)
    if error is Option.Some(error):
        panic(lexerErrorStr(error))
    let result = match try({ parseFn(tokens, 0) }):
        Result.Err(err): throw(TestError.ParseError(err))
        Result.Ok(result): result
    if result.newCursor != tokens.len():
        throw(TestError.Other("parser didn't consume all input, input len = `tokens.len()`, cursor after parsing = `result.newCursor`"))
    result.tree

runTest(
        testName: Str,
        input: Str,
        parseFn: Fn(Vec[Token], U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    ): exn ()
    print(testName)
    match try({ runParser(input, parseFn) }):
        Result.Ok(tree): print(tree.toDoc().print(80))
        Result.Err(err): print("ERR: `err`")
    print("")

runTest_(
        input: Str,
        parseFn: Fn(Vec[Token], U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    ): exn ()
    print(input)
    match try({ runParser(input, parseFn) }):
        Result.Ok(tree): print(tree.toDoc().print(80))
        Result.Err(err): print("ERR: `err`")
    print("")

lexerErrorStr(err: Error): Str
    "`err.loc.file`:`err.loc.line + 1`:`err.loc.col + 1`: `err.msg`"
