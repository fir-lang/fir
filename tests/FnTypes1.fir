prim type I32

test(i: I32): I32 = i

blah(): Fn(I32): exn I32 = test

f(): exn ()
    let x: Fn(I32): exn I32 = test
    test(123)

    let y: Fn(): exn Fn(I32): exn I32 = blah

# args: --typecheck --no-prelude
