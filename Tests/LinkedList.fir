type LinkList[t]:
    Cons(
        val: t,
        rest: LinkList[t],
    )
    Nil


impl[ToStr[t]] ToStr[LinkList[t]]:
    toStr(self: LinkList[t]) Str:
        match self:
            LinkList.Cons(val, rest): "`val` --> `rest`"
            LinkList.Nil: "Nil"


main():
    print(
        LinkList.Cons(
            val = u32(1),
            rest = LinkList.Cons(val = u32(2), rest = LinkList.Nil),
        ),
    )


# expected stdout: 1 --> 2 --> Nil
