# Regression test: `deep_normalize` impl matching must check ALL trait args, not
# just the first. With two impls that share the first arg but differ on the
# second, incorrect first-arg-only matching would pick the wrong impl.

trait Pair[a, b]:
    type Out

impl Pair[U32, U32]:
    type Out = U32

impl Pair[U32, Str]:
    type Out = Str

# `Pair[U32, Str].Out` should resolve to `Str` (second impl), not `U32`
# (first impl).
test(x: Pair[U32, Str].Out) Str:
    x

main():
    print(test("hello"))

# expected stdout:
# hello
