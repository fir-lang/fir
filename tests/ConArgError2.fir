type Option[t]:
    None
    Some(t)

f() Option[()]:
    Option.None

main():
    match f():
        Option.None(_): ()
        Option.Some(_): ()

# args: --typecheck --no-prelude
# expected exit status: 101
# expected stderr:
# tests/ConArgError2.fir:10:9: Type Option[_1] doesn't take arugments, but applied 1 arguments
