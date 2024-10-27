trait Iterator[T]:
    type Item

    fn next(self): Option[Item]

trait Step[T]:
    fn next(self): T

fn range[T](start: T, end: T): RangeIterator[T] =
    RangeIterator(current = start, end = end)

fn irange[T](start: T, end: T): InclusiveRangeIterator[T] =
    InclusiveRangeIterator(current = start, end = end)

type RangeIterator[T]:
    current: T
    end: T

impl[T: Step + Ord] Iterator for RangeIterator[T]:
    type Item = T

    fn next(self): Option[T] =
        if self.current >= self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.next()
            Option.Some(current)

type InclusiveRangeIterator[T]:
    current: T
    end: T

impl[T: Step + Ord] Iterator for InclusiveRangeIterator[T]:
    type Item = T

    fn next(self): Option[T] =
        if self.current > self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.next()
            Option.Some(current)
