import [
    Compiler/Error,
    Compiler/Lexer,
    Tool/Peg/PegTestLib,
    Tool/Peg/TestGrammarPreds,
    Tool/Peg/TestPreds,
]


main():
    let items1: Vec[Item[Defaults1]] = try(
        \(): runParser("a b", items, Bool.False),
    ).unwrap()

    print(items1)

    let items2: Vec[Item[Defaults2]] = try(
        \(): runParser("a b", items, Bool.False),
    ).unwrap()

    print(items2)


# expected stdout:
# [A(x = 0, rest = (def1Ext1 = 1)),B(msg = hi, rest = (def1Ext2 = Bool.True))]
# [A(x = 0, rest = (def2Ext1 = hi)),B(msg = hi, rest = (def2Ext2 = Option.Some(1)))]
