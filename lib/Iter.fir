trait Iterator[iter, item, errs]:
    next(self: iter): {..errs} Option[item]

    map(self: iter, f: Fn(item): {..errs} b): {..errs2} Map[iter, item, b, errs]
        Map(iter = self, f = f)

    peekable(self: iter): {..errs} Peekable[iter, item]
        Peekable(iter = self, peeked = Option.None)

    mapResult(self: iter, f: Fn(Result[[..errs], Option[item]]): {..errsNew} Option[b]): MapResult[iter, item, b, errs, errsNew]
        MapResult(iter = self, f = f)

    try(self: iter): Try[iter, item, errs]
        Try(iter = self)

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

# NOTE: The row type parameter needs to start with `recRow` to have kind `row(variant)`.
type Map[iter, a, b, recRowErrs]:
    iter: iter
    f: Fn(a): {..recRowErrs} b

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

type MapResult[iter, item, b, varRowErrsOld, varRowErrsNew]:
    iter: iter
    f: Fn(Result[[..varRowErrsOld], Option[item]]): {..varRowErrsNew} Option[b]

impl[Iterator[iter1, item1, varRowErrsOld1]] Iterator[MapResult[iter1, item1, b1, varRowErrsOld1, varRowErrsNew1], b1, varRowErrsNew1]:
    next(self: MapResult[iter1, item1, b1, varRowErrsOld1, varRowErrsNew1]): {..varRowErrsNew1} Option[b1]
        self.f(try(self.iter.next))

type Try[iter, item, errs]:
    iter: iter

impl[Iterator[iter1, item1, varRowErrs1]] Iterator[Try[iter1, item1, varRowErrs1], Result[[..varRowErrs1], item1], varRowErrs2]:
    next(self: Try[iter1, item1, varRowErrs1]): {..varRowErrs2} Option[Result[[..varRowErrs1], item1]]
        match try(fn(): {..varRowErrs1} Option[item1] { self.iter.next() }):
            Result.Err(err): Option.Some(Result.Err(err))
            Result.Ok(Option.Some(item)): Option.Some(Result.Ok(item))
            Result.Ok(Option.None): Option.None
