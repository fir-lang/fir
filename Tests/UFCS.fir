# Uniform Function Call Syntax (UFCS) allows calling top-level and local
# functions with the method call syntax.


main():
    # Direct UFCS call.
    Point(x = 1, y = 2).printPoint()

    # UFCS method-like chain.
    21.i32().double().print()

    # UFCS as a value (closure form): bare `a.f` with `f` a top-level fn.
    let f = 10.i32().double     # allocates closure, captures the argument of `double`
    f().print()                 # closure call

    # Polymorphic top-level functions via UFCS.
    let p = 7.i32().pair("hi")
    "(`p.fst`, `p.snd`)".print()

    # Polymorphic top-level function, converted to closure.
    let pFn = 8.i32().pair      # allocates closure, captures first argument to `pair`
    let p = pFn("hi")           # closure call
    "(`p.fst`, `p.snd`)".print()

    # Polymorphic top-level function, with explicit type arguments.
    let pFn = 9.i32().pair[I32, Str, []]
    let p = pFn("hi")
    "(`p.fst`, `p.snd`)".print()

    # Method precedence: `"abc".len()` uses `Str.len`, not the top-level `len`.
    "abc".len().print()

    # When there isn't a local with the same name, top-level functions are
    # called as methods.
    123.i32().pair("hi").pairToStr().print()    # calls top-level `pairToStr`

    # Local functions can also be used for UFCS and they have precedence over
    # top-level ones.
    let pairToStr = \(pair: (fst: I32, snd: Str)) Str:
        "(fst = `pair.fst`, snd = `pair.snd`) (local fn)"

    123.i32().pair("hi").pairToStr().print()    # calls local `pairToStr`

    # Using a lambda to pass named arguments, or as positional argument other
    # than the first.
    456.i32().apply(\(y): Point(x = 123, y)).printPoint()

    # At least for now, it's not possible to call associated functions with this
    # syntax. We have to use `apply`.
    range(u32(0), u32(5)).apply(\(iter): Vec.fromIter(iter)).print()


type Point(
    x: I32,
    y: I32,
)


printPoint(p: Point):
    printStr("(`p.x.toStr()`, `p.y.toStr()`)")


double(x: I32) I32:
    x * 2


pair[t, u](a: t, b: u) (fst: t, snd: u):
    (fst = a, snd = b)


pairToStr(pair: (fst: I32, snd: Str)) Str:
    "(fst = `pair.fst`, snd = `pair.snd`) (top-level fn)"


len(s: Str) U32:
    panic("Top-level len called")


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
# [0,1,2,3,4]
