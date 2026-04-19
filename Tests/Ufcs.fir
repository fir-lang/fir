type Point(
    x: I32,
    y: I32,
)


printPoint(p: Point):
    printStr("(`p.x.toStr()`, `p.y.toStr()`)")


double(x: I32) I32:
    x * 2


# Polymorphic top-level function.
pair[t, u](a: t, b: u) (fst: t, snd: u):
    (fst = a, snd = b)

pairToStr(pair: (fst: I32, snd: Str)) Str:
    "(fst = `pair.fst`, snd = `pair.snd`) (top-level fn)"

# Collides with `Vec.len`, method should have precedence.
len(s: Str) U32:
    s.len()


pass(x: t, f: Fn(t) ret / exn) ret / exn:
    f(x)


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

    123.i32().pair("hi").pairToStr().print()

    # Local functions can also be used for UFCS and they have precedence over
    # top-level ones.
    let pairToStr = \(pair: (fst: I32, snd: Str)) Str:
        "(fst = `pair.fst`, snd = `pair.snd`) (local fn)"

    123.i32().pair("hi").pairToStr().print()

    # Using a lambda to pass named arguments, or as positional argument other
    # than the first.
    456.i32().pass(\(y): Point(x = 123, y)).printPoint()

# expected stdout:
# (1, 2)
# 42
# 20
# (7, hi)
# (8, hi)
# (9, hi)
# 3
# (fst = 123, snd = hi) (top-level fn)
# (fst = 123, snd = hi) (local fn)
# (123, 456)
