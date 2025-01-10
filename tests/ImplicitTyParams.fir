fn id(a: t): t = a

fn f1(): Result[[E1, ..r], ()]
    Result.Err(`E1)

type X[t]:
    a: t

impl X[t]:
    fn f2(self, other: t): t
        self.a

    fn f3(self, other: t2): t2
        other

fn main() = ()
