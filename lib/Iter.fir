trait Iterator[iter, item, exn]:
    next(self: iter): exn Option[item]

    map(self: iter, f: Fn(item): exn b): Map[iter, item, b, exn]
        Map(iter = self, f = f)

    peekable(self: iter): Peekable[iter, item, exn]
        Peekable(iter = self, peeked = Option.None)

    mapResult(self: iter, f: Fn(Result[exn, Option[item]]): exn2 Option[b]): MapResult[iter, item, b, exn, exn2]
        MapResult(iter = self, f = f)

    try(self: iter): Try[iter, item, exn]
        Try(iter = self)

    # TODO: This currently can't be called because `item` is ambiguous, and
    # currently we have no way of specifying it.
    count(self: iter): exn U32
        let n = 0u32
        for _: item in self:
            n += 1
        n

    skip(self: iter, amount: U32): exn Skip[iter, item, exn]
        Skip(iter = self, amount)

trait Step[t]:
    step(self: t): t

range(start: t, end: t): RangeIterator[t]
    RangeIterator(current = start, end = end)

irange(start: t, end: t): InclusiveRangeIterator[t]
    InclusiveRangeIterator(current = start, end = end)

type RangeIterator[t]:
    current: t
    end: t

impl[Step[t], Ord[t]] Iterator[RangeIterator[t], t, exn]:
    next(self: RangeIterator[t]): exn Option[t]
        if self.current >= self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.step()
            Option.Some(current)

type InclusiveRangeIterator[t]:
    current: t
    end: t

impl[Step[t], Ord[t]] Iterator[InclusiveRangeIterator[t], t, exn]:
    next(self: InclusiveRangeIterator[t]): exn Option[t]
        if self.current > self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.step()
            Option.Some(current)

# NOTE: The row type parameter needs to start with `recRow` to have kind `row(variant)`.
type Map[iter, a, b, exn]:
    iter: iter
    f: Fn(a): exn b

# BUG(#86): To work around substitution bugs, give quantified variables
# different names than the quantified variables of `Iterator`.
impl[Iterator[iter1, a1, exn1]] Iterator[Map[iter1, a1, b1, exn1], b1, exn1]:
    next(self: Map[iter1, a1, b1, exn1]): exn1 Option[b1]
        match self.iter.next():
            Option.None: Option.None
            Option.Some(a): Option.Some(self.f(a))

type Peekable[iter, item, exn]:
    iter: iter
    peeked: Option[item]

impl[Iterator[iter, item, exn]] Iterator[Peekable[iter, item, exn], item, exn]:
    next(self: Peekable[iter, item, exn]): exn Option[item]
        match self.peeked:
            Option.Some(peeked):
                self.peeked = Option.None
                Option.Some(peeked)
            Option.None:
                self.iter.next()

Peekable.peek[Iterator[iter, item, exn]](self: Peekable[iter, item, exn]): exn Option[item]
    match self.peeked:
        Option.Some(peeked):
            Option.Some(peeked)
        Option.None:
            self.peeked = self.iter.next()
            self.peeked

type MapResult[iter, item, b, exnOld, exnNew]:
    iter: iter
    f: Fn(Result[exnOld, Option[item]]): exnNew Option[b]

impl[Iterator[iter1, item1, exnOld1]] Iterator[MapResult[iter1, item1, b1, exnOld1, exnNew1], b1, exnNew1]:
    next(self: MapResult[iter1, item1, b1, exnOld1, exnNew1]): exnNew1 Option[b1]
        self.f(try(self.iter.next))

type Try[iter, item, exn]:
    iter: iter

impl[Iterator[iter1, item1, exn1]] Iterator[Try[iter1, item1, exn1], Result[exn1, item1], exn2]:
    next(self: Try[iter1, item1, exn1]): exn2 Option[Result[exn1, item1]]
        match try(self.iter.next):
            Result.Err(err): Option.Some(Result.Err(err))
            Result.Ok(Option.Some(item)): Option.Some(Result.Ok(item))
            Result.Ok(Option.None): Option.None

type Skip[iter, item, exn]:
    iter: iter
    amount: U32

impl[Iterator[iter1, item1, exn1]] Iterator[Skip[iter1, item1, exn1], item1, exn1]:
    next(self: Skip[iter1, item1, exn1]): exn1 Option[item1]
        while self.amount != 0:
            let _: Option[item1] = self.iter.next()
            self.amount -= 1
        self.iter.next()
