trait T[A]:
    fn f[B: ToStrView](self, b: B)

type X:
    value: I32

impl T[X]:
    fn f[Q: ToStrView](self, q: Q) =
        printStr("X.f called with q = `q.toStrView()`")

fn main(input: Str) =
    let x = X(value = 123)
    x.f("hi")

    let y = x.f
    y(123)

# expected stdout:
# X.f called with q = hi
# X.f called with q = 123
