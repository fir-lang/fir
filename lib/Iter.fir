trait Iterator[t]:
    type Item

    fn next(self): Option[Item]

trait Step[t]:
    fn next(self): t

fn range[t](start: t, end: t): RangeIterator[t] =
    RangeIterator(current = start, end = end)

fn irange[t](start: t, end: t): InclusiveRangeIterator[t] =
    InclusiveRangeIterator(current = start, end = end)

type RangeIterator[t]:
    current: t
    end: t

impl[t: Step + Ord] Iterator for RangeIterator[t]:
    type Item = t

    fn next(self): Option[t] =
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

    fn next(self): Option[t] =
        if self.current > self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.next()
            Option.Some(current)
