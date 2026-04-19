type Point(
    x: I32,
    y: I32,
)


# Not a method of Point.
printPoint(p: Point):
    printStr("(`p.x.toStr()`, `p.y.toStr()`)")


double(x: I32) I32:
    x * 2


# Polymorphic top-level function.
pair[t, u](a: t, b: u) (fst: t, snd: u):
    (fst = a, snd = b)


# Collides with `Vec.len`, method should have precedence.
len(s: Str) U32:
    s.len()


main():
    # Direct UFCS call.
    Point(x = 1, y = 2).printPoint()

    # UFCS method-like chain.
    21.i32().double().print()

    # UFCS as a value (closure form): bare `a.f` with `f` a top-level fn.
    let f = 10.i32().double
    f().print()

    # Polymorphic top-level functions via UFCS.
    let p = 7.i32().pair("hi")
    "(`p.fst`, `p.snd`)".print()

    # Polymorphic top-level function, converted to closure.
    let pFn = 8.i32().pair
    let p = pFn("hi")
    "(`p.fst`, `p.snd`)".print()

    # Polymorphic top-level function, with explicit type arguments.
    let pFn = 9.i32().pair[I32, Str, []]
    let p = pFn("hi")
    "(`p.fst`, `p.snd`)".print()

    # Method precedence: `"abc".len()` uses `Str.len`, not the top-level `len`.
    "abc".len().print()


# expected stdout:
# (1, 2)
# 42
# 20
# (7, hi)
# (8, hi)
# (9, hi)
# 3
