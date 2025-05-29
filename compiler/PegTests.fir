import Lexer
import TestGrammar

main
    print("PEG TESTS")
    runTest("a", terminalA)
    runTest("b", terminalA)
    runTest("a b", terminalA)
    runTest("b", terminalB)
    runTest("a b", terminalAThenB)
    runTest("b", zeroOrMoreAThenB)
    runTest("a b", zeroOrMoreAThenB)
    runTest("a a b", zeroOrMoreAThenB)
    runTest("b", oneOrMoreAThenB)
    runTest("a b", oneOrMoreAThenB)
    runTest("a a b", oneOrMoreAThenB)
    runTest("a a b", zeroOrOneAThenB)
    runTest("a b", zeroOrOneAThenB)
    runTest("b", zeroOrOneAThenB)

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
        input: Str,
        parseFn: Fn(Vec[Token], U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    ): exn ()
    printNoNl("\tParsing \"`input`\"\t")
    match try({ runParser(input, parseFn) }):
        Result.Ok(tree): print("OK")
        Result.Err(err): print("ERR: `err`")

lexerErrorStr(err: Error): Str
    "`err.loc.file`:`err.loc.line + 1`:`err.loc.col + 1`: `err.msg`"
