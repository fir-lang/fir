type MyList[t](
    head: t,
    tail: Option[MyList[t]],
)


# - When solving goal `ToDoc[MyList[t]]`
# - This `impl` matches and generates subgoal `ToDoc[Option[MyList[t]]]`
# - `impl[ToDoc[t]] ToDoc[Option[t]]` matches and generates the original subgoal
#   `ToDoc[MyList[t]]`
impl[ToDoc[t], ToDoc[Option[MyList[t]]]] ToDoc[MyList[t]]:
    toDoc(self: MyList[t]) Doc:
        Doc.str("MyList(head = ")
            + self.head.toDoc()
            + Doc.str(", tail = ")
            + self.tail.toDoc()
            + Doc.char(')')


main():
    print(MyList(head = u32(123), tail = Option.None).toDoc().render(80))
    print(
        MyList(
            head = u32(123),
            tail = Option.Some(MyList(head = u32(456), tail = Option.None)),
        ).toDoc().render(80),
    )

# expected stdout:
# MyList(head = 123, tail = Option.None)
# MyList(head = 123, tail = Option.Some(MyList(head = 456, tail = Option.None)))
