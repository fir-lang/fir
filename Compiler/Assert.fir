value type AssertionError(
    msg: Str,
)


assertEq[Eq[t], ToStr[t]](expected: t, found: t):
    if expected != found:
        throwUnchecked(
            ~AssertionError(msg = "Expected `expected`, found `found`"),
        )


assert(cond: Bool):
    if not cond:
        panic("Assertion failure")
