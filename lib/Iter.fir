trait Iterator[t]:
    type Item

    next(self): Option[Item]

trait Step[t]:
    next(self): t

range(start: t, end: t): RangeIterator[t]
    RangeIterator(current = start, end = end)

irange(start: t, end: t): InclusiveRangeIterator[t]
    InclusiveRangeIterator(current = start, end = end)

type RangeIterator[t]:
    current: t
    end: t

impl[t: Step + Ord] Iterator for RangeIterator[t]:
    type Item = t

    next(self): Option[t]
        if self.current >= self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.next()
            Option.Some(current)

type InclusiveRangeIterator[t]:
    current: t
    end: t

impl[t: Step + Ord] Iterator for InclusiveRangeIterator[t]:
    type Item = t

    next(self): Option[t]
        if self.current > self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.next()
            Option.Some(current)
