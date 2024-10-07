prim type I32

fn test(i: I32): I32 = i

fn blah(): Fn(I32): I32 = test

fn f() =
    let x: Fn(I32): I32 = test
    test(123)

    let y: Fn(): Fn(I32): I32 = blah

# args: --typecheck --no-prelude
