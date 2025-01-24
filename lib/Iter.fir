trait Iterator[t]:
    type Item

    next(self): Option[Item]

    map(self, f: Fn(Item): b): Map[t, Item, b]
        Map(iter = self, f = f)

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

type Map[i, a, b]:
    iter: i
    f: Fn(a): b

impl[a, b, i: Iterator[Item = a]] Iterator for Map[i, a, b]:
    type Item = b

    next(self): Option[b]
        match self.iter.next():
            Option.None: Option.None
            Option.Some(a): Option.Some(self.f(a))
