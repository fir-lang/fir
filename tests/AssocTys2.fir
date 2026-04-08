#[NoImplicitPrelude]
import []

trait Foo[t]:
    type A

prim type U32

prim type U64

impl Foo[U32]:
    type A = U64

# args: --typecheck
