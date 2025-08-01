# This program tests PEG parser generator, using the test grammar in TestGrammar.peg, compiled to
# TestGrammar.fir.
#
# Without vector literals it's painful to compare parse trees with expected trees, so for now, this
# prints parse trees, which we then compare with expected output using `goldentests`.

import Compiler.Error
import Compiler.Lexer
import PegTestLib
import TestGrammar

main():
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
    runTest("'b' as oneOrMoreAThenB (should fail)", "b", oneOrMoreAThenB)
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
    runTest("'b' as negLookahead", "b", negLookahead)
    runTest("'a' as negLookahead (should fail)", "a", negLookahead)
    runTest("'a a c' as oneOrMoreAThenB (should fail)", "a a c", oneOrMoreAThenB)
    runTest("'a b' as endOfInputTest", "a b", endOfInputTest)
    runTest("'a b ' as endOfInputTest", "a b ", endOfInputTest)
    runTest("'a b a' as endOfInputTest (should fail)", "a b a", endOfInputTest)
    runTest("'b a a a c b' as bracketedOneOrMoreA (should fail)", "b a a a c b", bracketedOneOrMoreA)

    print("# Simple cases -------------------------------------------")
    print(try(||: runParser("a", semanticActionSimple, Bool.False)))
    print(try(||: runParser("b", semanticActionSimple, Bool.False)))
    print(try(||: runParser("c", semanticActionSimple, Bool.False)))

    print("# Zero or more -------------------------------------------")
    print(try(||: runParser("", semanticActionZeroOrMore, Bool.False)))
    print(try(||: runParser("a", semanticActionZeroOrMore, Bool.False)))
    print(try(||: runParser("a b", semanticActionZeroOrMore, Bool.False)))

    print("# One or more --------------------------------------------")
    print(try(||: runParser("", semanticActionOneOrMore, Bool.False)))
    print(try(||: runParser("a", semanticActionOneOrMore, Bool.False)))
    print(try(||: runParser("a b", semanticActionOneOrMore, Bool.False)))

    print("# Group --------------------------------------------------")
    print(try(||: runParser("a a b b", semanticActionGroup, Bool.False)))

    print("# Optional -----------------------------------------------")
    print(try(||: runParser("a", semanticActionOptional, Bool.False)))
    print(try(||: runParser("", semanticActionOptional, Bool.False)))

    print("# Complex group ------------------------------------------")
    match try(||: runParser("a a a b b b c", semanticActionComplex, Bool.False)):
        Result.Err(err):
            print(err)
        Result.Ok(result):
            print("aVec = `result.aVec`")
            print("bVec = `result.bVec`")
            print("cOpt = `result.cOpt`")

# args: -iCompiler=compiler -iPeg=tools/peg
# expected stdout:
# 'a' as terminalA
# TerminalA(LowerId(1:1:"a"))
# 
# 'b' as terminalA (should fail)
# ERR: unexpected token or end of input at cursor 0
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
# ERR: unexpected token or end of input at cursor 0
# 
# 'b b' as terminalAThenB (should fail)
# ERR: unexpected token or end of input at cursor 0
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
# 'b' as oneOrMoreAThenB (should fail)
# ERR: unexpected token or end of input at cursor 0
# 
# 'a b' as oneOrMoreAThenB
# OneOrMoreAThenB(LowerId(1:1:"a"), LowerId(1:3:"b"))
# 
# 'a a b' as oneOrMoreAThenB
# OneOrMoreAThenB(LowerId(1:1:"a"), LowerId(1:3:"a"), LowerId(1:5:"b"))
# 
# 'a a b' as zeroOrOneAThenB
# ERR: unexpected token or end of input at cursor 1
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
# 
# 'b' as negLookahead
# NegLookahead(TerminalAOrB(LowerId(1:1:"b")))
# 
# 'a' as negLookahead (should fail)
# ERR: unexpected token or end of input at cursor 0
# 
# 'a a c' as oneOrMoreAThenB (should fail)
# ERR: unexpected token or end of input at cursor 2
# 
# 'a b' as endOfInputTest
# EndOfInputTest(LowerId(1:1:"a"), LowerId(1:3:"b"))
# 
# 'a b ' as endOfInputTest
# EndOfInputTest(LowerId(1:1:"a"), LowerId(1:3:"b"))
# 
# 'a b a' as endOfInputTest (should fail)
# ERR: unexpected token or end of input at cursor 2
# 
# 'b a a a c b' as bracketedOneOrMoreA (should fail)
# ERR: unexpected token or end of input at cursor 4
# 
# # Simple cases -------------------------------------------
# Result.Ok('a')
# Result.Ok('b')
# Result.Err(unexpected token or end of input at cursor 0)
# # Zero or more -------------------------------------------
# Result.Ok([])
# Result.Ok(['a'])
# Result.Ok(['a','b'])
# # One or more --------------------------------------------
# Result.Err(unexpected token or end of input at cursor 0)
# Result.Ok(['a'])
# Result.Ok(['a','b'])
# # Group --------------------------------------------------
# Result.Ok([a,b])
# # Optional -----------------------------------------------
# Result.Ok(Option.Some(LowerId(1:1:"a")))
# Result.Ok(Option.None)
# # Complex group ------------------------------------------
# aVec = [LowerId(1:3:"a"),LowerId(1:5:"a")]
# bVec = [LowerId(1:7:"b"),LowerId(1:9:"b"),LowerId(1:11:"b")]
# cOpt = Option.Some(LowerId(1:13:"c"))
