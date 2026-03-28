type Pair(fst: U32, snd: U32)

mkRecord() (p: Pair, label: Str):
    (p = Pair(fst = 10, snd = 20), label = "test")

main():
    let (p = Pair(fst, snd), ..rest) = mkRecord()
    print(fst)
    print(snd)
    print(rest.label)

# expected stdout:
# 10
# 20
# test
