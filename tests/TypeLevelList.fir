type Cons[head, tail]

type Nil

trait TypeLevelListLen[t]:
    len() U32

impl TypeLevelListLen[Nil]:
    len() U32:
        0

impl[TypeLevelListLen[tail]] TypeLevelListLen[Cons[head, tail]]:
    len() U32 / exn:
        u32(1) + TypeLevelListLen.len[tail, exn]()

main():
    print(TypeLevelListLen.len[Cons[U8, Cons[U32, Cons[U64, Nil]]], []]())

# expected stdout: 3
