trait T[A]:
    fn f[B: ToStrView](self, b: B)

type X:
    value: I32

impl T[X]:
    fn f[Q: ToStrView](self, q: Q) =
        printStr("X.f called with q = `q`")

fn main(input: Str) =
    let x = X(value = 123)
    x.f("hi")

# Interpreter panics, for now just type check.
# args: --typecheck
