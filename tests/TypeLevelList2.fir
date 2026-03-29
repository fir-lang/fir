main():
    print(
        ListCons(
            head = u32(1),
            tail = ListCons(head = Bool.True, tail = ListCons(head = "hi", tail = ListNil)),
        ).typeLevelListToStr(),
    )

# expected stdout: 1 -> Bool.True -> hi -> []
