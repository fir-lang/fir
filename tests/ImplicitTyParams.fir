id(a: t): t = a

f1(): Result[[E1, ..r], ()]
    Result.Err(~E1)

type X[t]:
    a: t

X.f2(self: X[t], other: t): t
    self.a

X.f3(self: X[t], other: t2): t2
    other

trait Test[t]:
    f: a
    x: Fn(a): {..r} b

main() = ()
