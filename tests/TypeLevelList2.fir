type Cons[head, tail](
    head: head,
    tail: tail,
)

type Nil

trait TypeLevelListToStr[t]:
    typeLevelListToStr(self: t) Str

impl TypeLevelListToStr[Nil]:
    typeLevelListToStr(self: Nil) Str:
        "[]"

impl[ToStr[head], TypeLevelListToStr[tail]] TypeLevelListToStr[Cons[head, tail]]:
    typeLevelListToStr(self: Cons[head, tail]) Str:
        "`self.head` -> `self.tail.typeLevelListToStr()`"

main():
    print(
        Cons(
            head = u32(1),
            tail = Cons(head = Bool.True, tail = Cons(head = "hi", tail = Nil)),
        ).typeLevelListToStr(),
    )

# expected stdout: 1 -> Bool.True -> hi -> []
