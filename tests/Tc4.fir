prim type I32

prim fn printI32(i: I32)

type Option[T]:
    Some(T)
    None

fn test() =
    let x = Option.Some(123)
    match x:
        Option.Some(a): printI32(a)
        Option.None: ()

# args: --typecheck --no-prelude
