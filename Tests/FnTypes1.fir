#[NoImplicitPrelude]
import []

type Type1

test(i: Type1) Type1: i

blah() (Fn(Type1) Type1 / exn): test

f() () / exn:
    let x: Fn(Type1) Type1 / exn = test
    test(Type1)

    let y: Fn() (Fn(Type1) Type1 / exn) / exn = blah

# args: --typecheck
