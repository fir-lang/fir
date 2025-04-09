trait Iterator[iter, item, errs]:
    next(self: iter): {..errs} Option[item]

    map(self: iter, f: Fn(item): b): {..errs} Map[iter, item, b]
        Map(iter = self, f = f)

    peekable(self: iter): {..errs} Peekable[iter, item]
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

impl[Step[t], Ord[t]] Iterator[RangeIterator[t], t, errs]:
    next(self: RangeIterator[t]): {..errs} Option[t]
        if self.current >= self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.step()
            Option.Some(current)

type InclusiveRangeIterator[t]:
    current: t
    end: t

impl[Step[t], Ord[t]] Iterator[InclusiveRangeIterator[t], t, errs]:
    next(self: InclusiveRangeIterator[t]): {..errs} Option[t]
        if self.current > self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.step()
            Option.Some(current)

type Map[iter, a, b]:
    iter: iter
    f: Fn(a): b

impl[Iterator[iter, a, errs]] Iterator[Map[iter, a, b], b, errs]:
    next(self: Map[iter, a, b]): {..errs} Option[b]
        match self.iter.next():
            Option.None: Option.None
            Option.Some(a): Option.Some(self.f(a))

type Peekable[iter, item]:
    iter: iter
    peeked: Option[item]

impl[Iterator[iter, item, errs]] Iterator[Peekable[iter, item], item, errs]:
    next(self: Peekable[iter, item]): {..errs} Option[item]
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
