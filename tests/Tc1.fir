#[NoImplicitPrelude]
import []

type Type1

type T[a](field: a)

test() T[Type1]:
    T(field = Type1)

# args: --typecheck
