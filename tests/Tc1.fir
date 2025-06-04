prim type I32

type T[a]:
    field: a

test() T[I32]:
    T(field = 123)

# args: --typecheck --no-prelude
