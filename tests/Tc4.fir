#[NoImplicitPrelude]
import []

type Type1

prim printI32(i: Type1)

type Option[t]:
    Some(t)
    None

test():
    let x = Option.Some(Type1)
    match x:
        Option.Some(a): printI32(a)
        Option.None: ()

# args: --typecheck
