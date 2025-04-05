trait Iterator[iter, item]:
    next(self: iter): Option[item]

    map(self: iter, f: Fn(item): b): Map[iter, item, b]
        Map(iter = self, f = f)

    peekable(self: iter): Peekable[iter, item]
        Peekable(iter = self, peeked = Option.None)

trait Step[t]:
    step(self: t): t

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
            self.current = self.current.step()
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
            self.current = self.current.step()
            Option.Some(current)

type Map[iter, a, b]:
    iter: iter
    f: Fn(a): b

impl[Iterator[iter, a]] Iterator[Map[iter, a, b], b]:
    next(self: Map[iter, a, b]): Option[b]
        match self.iter.next():
            Option.None: Option.None
            Option.Some(a): Option.Some(self.f(a))

type Peekable[iter, item]:
    iter: iter
    peeked: Option[item]

impl[Iterator[iter, item]] Iterator[Peekable[iter, item], item]:
    next(self: Peekable[iter, item]): Option[item]
        match self.peeked:
            Option.Some(peeked):
                self.peeked = Option.None
                Option.Some(peeked)
            Option.None:
                self.iter.next()

Peekable.peek[Iterator[iter, item]](self: Peekable[iter, item]): Option[item]
    match self.peeked:
        Option.Some(peeked):
            Option.Some(peeked)
        Option.None:
            self.peeked = self.iter.next()
            self.peeked
