trait T[a]:
    f[ToStr[b]](self: a, b: b)

type X(val: I32)

impl T[X]:
    f[ToStr[q]](self: X, q: q):
        printStr("X.f called with q = `q`")

main():
    let x = X(val = 123)
    x.f("hi")

    let y = x.f
    y(123)

# expected stdout:
# X.f called with q = hi
# X.f called with q = 123
