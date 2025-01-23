id(a: t): t = a

f1(): Result[[E1, ..r], ()]
    Result.Err(~E1)

type X[t]:
    a: t

X[t].f2(self, other: t): t
    self.a

X[t].f3(self, other: t2): t2
    other

trait Test[t]:
    f: a
    x: Fn(a): {..r} b

main() = ()
