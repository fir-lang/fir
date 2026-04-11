#[NoImplicitPrelude]
import []


#[path = Fir/Prim/U32]
prim type U32


#[derive(ToDoc, Eq)]
type Foo(x: U32, y: U32)


#[just(arg = Testing) + 1]
type X = U32


# args: --parse
