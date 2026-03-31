# Tests unifying an empty anonymous row with an associated type of row kind.
# When pattern matching a constructor with a row-kinded associated type
# extension, the empty rest pattern `..` creates `row(..r)` which must unify
# with the associated type (not just rigid type variables).

trait HasRow[t]:
    type R: Row[Rec]

type Wrapper[t]:
    Wrap(x: I32, ..HasRow[t].R)

type Foo

impl HasRow[Foo]:
    type R = row(y: Str)

getX[HasRow[t]](w: Wrapper[t]) I32:
    match w:
        Wrapper.Wrap(x = n, ..): n

main():
    print(getX(Wrapper.Wrap[Foo](x = 123, y = "hello")))

# expected stdout:
# 123
