assertEq[Eq[t], ToStr[t]](expected: t, found: t):
    if expected != found:
        throwUnchecked(~AssertionError(msg = "Expected `expected`, found `found`"))
