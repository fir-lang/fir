import [
    Compiler/Error,
    Compiler/Lexer,
    Tool/Peg/PegTestLib,
    Tool/Peg/TestGrammarState,
]


main():
    let state = UserState(a = 0, b = 0, c = 0)
    runTestState("Simple", "a b c", abcs, state)
    print(state)


type UserState(
    a: U32,
    b: U32,
    c: U32,
)


impl ToStr[UserState]:
    toStr(self: UserState) Str:
        "UserState(a = `self.a`, b = `self.b`, c = `self.c`)"


# expected stdout:
# Simple
# ()
# 
# UserState(a = 1, b = 1, c = 1)
