prim type I32

test(i: I32) I32: i

blah() (Fn(I32) I32 / exn): test

f() () / exn:
    let x: Fn(I32) I32 / exn = test
    test(123)

    let y: Fn() (Fn(I32) I32 / exn) / exn = blah

# args: --typecheck --no-prelude
