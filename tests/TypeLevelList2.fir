main():
    print(
        ListCons(
            head = u32(1),
            tail = Option.Some(ListCons(
                head = Bool.True,
                tail = Option.Some(ListCons(head = "hi", tail = Option.None[[]]))
            )),
        ),
    )

# expected stdout: 1, Bool.True, hi
