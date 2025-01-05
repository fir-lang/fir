prim type I32

type T[a]:
    field: a

fn test(): T[I32] =
    T(field = 123)

# args: --typecheck --no-prelude
