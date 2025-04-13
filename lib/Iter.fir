trait Iterator[iter, item, errs]:
    next(self: iter): {..errs} Option[item]

    map(self: iter, f: Fn(item): {..errs} b): {..errs2} Map[iter, item, b, errs]
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

type Map[iter, a, b, errs]:
    iter: iter
    f: Fn(a): {..errs} b

# BUG(#86): To work around substitution bugs, give quantified variables
# different names than the quantified variables of `Iterator`.
impl[Iterator[iter1, a1, errs1]] Iterator[Map[iter1, a1, b1, errs1], b1, errs1]:
    next(self: Map[iter1, a1, b1, errs1]): {..errs1} Option[b1]
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

Peekable.peek[Iterator[iter, item, errs]](self: Peekable[iter, item]): {..errs} Option[item]
    match self.peeked:
        Option.Some(peeked):
            Option.Some(peeked)
        Option.None:
            self.peeked = self.iter.next()
            self.peeked
