trait Iterator[iter, item]:
    next(self: iter): Option[item]

    map(self: iter, f: Fn(item): b): Map[iter, item, b]
        Map(iter = self, f = f)

trait Step[t]:
    next(self: t): t

range(start: t, end: t): RangeIterator[t]
    RangeIterator(current = start, end = end)

irange(start: t, end: t): InclusiveRangeIterator[t]
    InclusiveRangeIterator(current = start, end = end)

type RangeIterator[t]:
    current: t
    end: t

impl[Step[t], Ord[t]] Iterator[RangeIterator[t], t]:
    next(self: RangeIterator[t]): Option[t]
        if self.current >= self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.next()
            Option.Some(current)

type InclusiveRangeIterator[t]:
    current: t
    end: t

impl[Step[t], Ord[t]] Iterator[InclusiveRangeIterator[t], t]:
    next(self: InclusiveRangeIterator[t]): Option[t]
        if self.current > self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.next()
            Option.Some(current)

type Map[iter, a, b]:
    iter: iter
    f: Fn(a): b

impl[Iterator[iter, a]] Iterator[Map[iter, a, b], b]:
    next(self: Map[iter, a, b]): Option[b]
        match self.iter.next():
            Option.None: Option.None
            Option.Some(a): Option.Some(self.f(a))
