main():
    print(
        ListCons(
            head = u32(1),
            tail = ListCons(head = Bool.True, tail = ListCons(head = "hi", tail = ListNil)),
        ),
    )

# expected stdout: 1 -> Bool.True -> hi -> []
