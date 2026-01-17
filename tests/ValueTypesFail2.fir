value type List[t]:
    Cons(
        val: t,
        rest: List[t],
    )
    Nil

# args: --typecheck
# expected exit status: 101
# expected stderr: Value type List has infinite size due to recursion
