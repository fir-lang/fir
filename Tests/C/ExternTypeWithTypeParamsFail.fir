import [Fir/C as C]


extern type Pair[a, b] = "struct pair"(
    fst: a = "fst",
    snd: b = "snd",
)


main():
    printStr("ok")


# expected exit status: 101
# expected stderr:
# Tests/C/ExternTypeWithTypeParamsFail.fir:4:13: Unexpected token UpperIdLBracket ("Pair")
