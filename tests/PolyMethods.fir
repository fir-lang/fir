trait T[a]:
    fn f[b: ToStr](self, b: b)

type X:
    value: I32

impl T for X:
    fn f[q: ToStr](self, q: q)
        printStr("X.f called with q = `q`")

fn main()
    let x = X(value = 123)
    x.f("hi")

    let y = x.f
    y(123)

# expected stdout:
# X.f called with q = hi
# X.f called with q = 123
