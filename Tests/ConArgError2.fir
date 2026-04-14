#[NoImplicitPrelude]
import []

type Option[t]:
    None
    Some(t)

f() Option[()]:
    Option.None

main():
    match f():
        Option.None(_): ()
        Option.Some(_): ()

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Tests/ConArgError2.fir:13:9: Type Option[_1] doesn't take arguments, but applied 1 arguments
