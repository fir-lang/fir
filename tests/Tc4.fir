prim type I32

prim printI32(i: I32)

type Option[t]:
    Some(t)
    None

test():
    let x = Option.Some(123)
    match x:
        Option.Some(a): printI32(a)
        Option.None: ()

# args: --typecheck --no-prelude
