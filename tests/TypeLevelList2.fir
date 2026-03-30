main():
    print(
        List(
            head = u32(1),
            tail =
                Option.Some(
                    List(
                        head = Bool.True,
                        tail =
                            Option.Some(
                                List(head = "hi", tail = Option.None[[]]),
                            ),
                    ),
                ),
        ),
    )


# expected stdout: 1, Bool.True, hi
