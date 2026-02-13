import [
    Compiler/Error,
    Compiler/Lexer,
    Tool/Peg/PegTestLib,
    Tool/Peg/TestGrammarState,
    Tool/Peg/TestState,
]


main():
    let state = UserState(a = 0, b = 0, c = 0)
    runTestState("Simple", "a b c", abcs, state)
    print(state)


# expected stdout:
# Simple
# ()
# 
# UserState(a = 1, b = 1, c = 1)
