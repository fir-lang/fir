value type LinkList[t]:
    Cons(
        val: t,
        rest: LinkList[t],
    )
    Nil


# args: --typecheck
# expected exit status: 101
# expected stderr: Value type LinkList has infinite size due to recursion
