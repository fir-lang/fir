# This program tests PEG parser generator, using the test grammar in TestGrammar.peg, compiled to
# TestGrammar.fir.
#
# Without vector literals it's painful to compare parse trees with expected trees, so for now, this
# prints parse trees, which we then compare with expected output using `goldentests`.

import Lexer
import TestGrammar

main
    runTest("'a' as terminalA", "a", terminalA)
    runTest("'b' as terminalA (should fail)", "b", terminalA)
    runTest("'a b' as terminalA (should fail)", "a b", terminalA)
    runTest("'b' as terminalB", "b", terminalB)
    runTest("'a' as terminalAOrB", "a", terminalAOrB)
    runTest("'b' as terminalAOrB", "b", terminalAOrB)
    runTest("'c' as terminalAOrB (should fail)", "c", terminalAOrB)
    runTest("'b b' as terminalAThenB (should fail)", "b b", terminalAThenB)
    runTest("'a b' as terminalAThenB", "a b", terminalAThenB)
    runTest("'b' as zeroOrMOreAThenB", "b", zeroOrMoreAThenB)
    runTest("'a b' as zeroOrMoreAThenB", "a b", zeroOrMoreAThenB)
    runTest("'a a b' as zeroOrMoreAThenB", "a a b", zeroOrMoreAThenB)
    runTest("'b' as oneOrMoreAThenB", "b", oneOrMoreAThenB)
    runTest("'a b' as oneOrMoreAThenB", "a b", oneOrMoreAThenB)
    runTest("'a a b' as oneOrMoreAThenB", "a a b", oneOrMoreAThenB)
    runTest("'a a b' as zeroOrOneAThenB", "a a b", zeroOrOneAThenB)
    runTest("'a b' as zeroOrOneAThenB", "a b", zeroOrOneAThenB)
    runTest("'b' as zeroOrOneAThenB", "b", zeroOrOneAThenB)
    runTest("'a b' as ignoreAThenB", "a b", ignoreAThenB)
    runTest("'a b' as ignoreGroupAThenB", "a b", ignoreGroupAThenB)
    runTest("'a a' as nonTerminals", "a a", nonTerminals)
    runTest("'a b' as nonTerminals", "a b", nonTerminals)
    runTest("'c a' as nonTerminalsBacktrack", "c a", nonTerminalsBacktrack)

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

lexerErrorStr(err: Error): Str
    "`err.loc.file`:`err.loc.line + 1`:`err.loc.col + 1`: `err.msg`"

# expected stdout:
# 'a' as terminalA
# TerminalA(LowerId(1:1:"a"))
# 
# 'b' as terminalA (should fail)
# ERR: unexpected token LowerId(1:1:"b")
# 
# 'a b' as terminalA (should fail)
# ERR: parser didn't consume all input, input len = 2, cursor after parsing = 1
# 
# 'b' as terminalB
# TerminalB(LowerId(1:1:"b"))
# 
# 'a' as terminalAOrB
# TerminalAOrB(LowerId(1:1:"a"))
# 
# 'b' as terminalAOrB
# TerminalAOrB(LowerId(1:1:"b"))
# 
# 'c' as terminalAOrB (should fail)
# ERR: unexpected token LowerId(1:1:"c")
# 
# 'b b' as terminalAThenB (should fail)
# ERR: unexpected token LowerId(1:1:"b")
# 
# 'a b' as terminalAThenB
# TerminalAThenB(LowerId(1:1:"a"), LowerId(1:3:"b"))
# 
# 'b' as zeroOrMOreAThenB
# ZeroOrMoreAThenB(LowerId(1:1:"b"))
# 
# 'a b' as zeroOrMoreAThenB
# ZeroOrMoreAThenB(LowerId(1:1:"a"), LowerId(1:3:"b"))
# 
# 'a a b' as zeroOrMoreAThenB
# ZeroOrMoreAThenB(LowerId(1:1:"a"), LowerId(1:3:"a"), LowerId(1:5:"b"))
# 
# 'b' as oneOrMoreAThenB
# ERR: unexpected token LowerId(1:1:"b")
# 
# 'a b' as oneOrMoreAThenB
# OneOrMoreAThenB(LowerId(1:1:"a"), LowerId(1:3:"b"))
# 
# 'a a b' as oneOrMoreAThenB
# OneOrMoreAThenB(LowerId(1:1:"a"), LowerId(1:3:"a"), LowerId(1:5:"b"))
# 
# 'a a b' as zeroOrOneAThenB
# ERR: unexpected token LowerId(1:1:"a")
# 
# 'a b' as zeroOrOneAThenB
# ZeroOrOneAThenB(LowerId(1:1:"a"), LowerId(1:3:"b"))
# 
# 'b' as zeroOrOneAThenB
# ZeroOrOneAThenB(LowerId(1:1:"b"))
# 
# 'a b' as ignoreAThenB
# IgnoreAThenB(LowerId(1:3:"b"))
# 
# 'a b' as ignoreGroupAThenB
# IgnoreGroupAThenB
# 
# 'a a' as nonTerminals
# NonTerminals(TerminalAOrB(LowerId(1:1:"a")), TerminalAOrB(LowerId(1:3:"a")))
# 
# 'a b' as nonTerminals
# NonTerminals(TerminalAOrB(LowerId(1:1:"a")), TerminalAOrB(LowerId(1:3:"b")))
# 
# 'c a' as nonTerminalsBacktrack
# NonTerminalsBacktrack(LowerId(1:1:"c"), LowerId(1:3:"a"))

# expected stderr: compiler/Token.fir:110:9: Unexhaustive pattern match
