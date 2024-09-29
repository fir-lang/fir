trait T[A]:
    fn f[B: ToStr](self, b: B)

type X:
    value: I32

impl T for X:
    fn f[Q: ToStr](self, q: Q) =
        printStr("X.f called with q = `q.toStr()`")

fn main() =
    let x = X(value = 123)
    x.f("hi")

    let y = x.f
    y(123)

# expected stdout:
# X.f called with q = hi
# X.f called with q = 123
