trait Step[T]:
    fn next(self): T

fn range[T: Step](start: T, end: T): RangeIterator[T] =
    RangeIterator(current = start, end = end)

type RangeIterator[T]:
    current: T
    end: T

impl[T: Step + Eq] Iterator for RangeIterator[T]:
    type Item = T

    fn next(self): Option[T] =
        if self.current == self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.next()
            Option.Some(current)

# args: --typecheck
