type List[t]:
    Cons(
        val: t,
        rest: List[t],
    )
    Nil


impl[ToStr[t]] ToStr[List[t]]:
    toStr(self: List[t]) Str:
        match self:
            List.Cons(val, rest): "`val` --> `rest`"
            List.Nil: "Nil"


main():
    print(List.Cons(val = u32(1), rest = List.Cons(val = u32(2), rest = List.Nil)))


