fn fac1(n: I32): I32 =
    let ret = 1
    for i in 2 ..= n:
        ret *= i
    ret

fn fac2(n: I32): I32 =
    let ret = 1
    for i in 2 .. n + 1:
        ret *= i
    ret

#|
for x in y: ...

generates typing:

y: Iterator[Item = A]
x: A

To support `range` function we need a new trait `Step`:

trait Step[T]:
    fn next(self): T

fn range[T: Step](start: T, end: T) = RangeIterator(current = T, end = T)

type RangeIterator[T]:
    current: T
    end: T

impl[T: Step] Iterator for RangeIterator[T]:
    type Item = T

    fn next(self): Option[T] =
        match self.current.cmp(self.end):
            Ordering.Eq:
                None
            _:
                let current = self.current
                self.current = self.current.next()
                Some(current)
|#

fn main() =
    printStr(fac1(0).toStr())
    printStr(fac1(5).toStr())
    printStr(fac1(10).toStr())

    printStr(fac2(0).toStr())
    printStr(fac2(5).toStr())
    printStr(fac2(10).toStr())

# expected stdout:
# 1
# 120
# 3628800
# 1
# 120
# 3628800
