prim type I32

test(i: I32): I32 = i

blah(): Fn(I32): I32 = test

f()
    let x: Fn(I32): I32 = test
    test(123)

    let y: Fn(): Fn(I32): I32 = blah

# args: --typecheck --no-prelude
