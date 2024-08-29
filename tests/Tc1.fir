prim type I32

type T[A]:
    field: A

fn test(): T[I32] =
    T(field = 123)

# args: --typecheck --no-prelude
