trait Iterator[iter, item, exn]:
    next(self: iter) Option[item] / exn

    map(self: iter, f: Fn(item) b / exn) Map[iter, item, b, exn]:
        Map(iter = self, f = f)

    peekable(self: iter) Peekable[iter, item, exn]:
        Peekable(iter = self, peeked = Option.None)

    mapResult(self: iter, f: Fn(Result[exn, Option[item]]) Option[b] / exn2) MapResult[iter, item, b, exn, exn2]:
        MapResult(iter = self, f = f)

    try(self: iter) Try[iter, item, exn]:
        Try(iter = self)

    skip(self: iter, amount: U32) Skip[iter, item, exn] / exn:
        Skip(iter = self, amount)

    any(self: iter, f: Fn(item) Bool / exn) Bool / exn:
        for item: item in self:
            if f(item):
                return Bool.True
        Bool.False

    all(self: iter, f: Fn(item) Bool / exn) Bool / exn:
        for item: item in self:
            if not f(item):
                return Bool.False
        Bool.True

    chain(self: iter, other: other) Chain[iter, other, item, exn]:
        Chain(iter1 = Option.Some(self), iter2 = Option.Some(other))

    filter(self: iter, f: Fn(item) Bool / exn) Filter[iter, item, exn]:
        Filter(iter = self, f = f)

    ## Count number of elements the iterator yields.
    ##
    ## Note that this consumes the iterator. The iterator won't yield any more elements after
    ## calling this method.
    ##
    ## See also `size` for a version of this that returns the number of elements without consuming
    ## the iterator.
    count(self: iter) U32 / exn:
        let n = u32(0)
        for _: item in self:
            n += 1
        n

    ## The number of elements the iterator will yield.
    ##
    ## Not all iterators know the number, and some iterators can yield infinitely. Those iterators
    ## will return `None`.
    ##
    ## This method does not consume the iterator.
    ##
    ## If an iterator returns a `Option.Some(n)`, it should always yield `n` elements. It's a bug if
    ## the iterator yields less or more.
    ##
    ## Order of type arguments: iter, item, exn (from `Iterator`), the function's exn.
    size(self: iter) Option[U32]:
        Option.None

    enumerate(self: iter) Enumerate[iter, item, exn]:
        Enumerate(iter = self, idx = 0)

    find(self: iter, pred: Fn(item) Bool / exn) Option[item] / exn:
        for item: item in self:
            if pred(item):
                return Option.Some(item)
        Option.None

    take(self: iter, n: U32) Take[iter, item, exn]:
        Take(iter = self, n)


# --------------------------------------------------------------------------------------------------


trait Step[t]:
    step(self: t) t

    ## If the number of steps (iterations) between `self` and `end` is known and
    ## it fits into an `U32`, this gives the number of steps. Otherwise it
    ## returns `Option.None`.
    ##
    ## This is mainly useful for implementing `RangeIterator.size`, which is
    ## necessary to be able to allocate `Array`s from `RangeIterator`s.
    stepsBetween(self: t, end: t) Option[U32]:
        Option.None


range(start: t, end: t) RangeIterator[t]:
    RangeIterator(current = start, end = end)


irange(start: t, end: t) InclusiveRangeIterator[t]:
    InclusiveRangeIterator(current = start, end = end)


type RangeIterator[t](
    current: t,
    end: t,
)


impl[Step[t], Ord[t]] Iterator[RangeIterator[t], t, exn]:
    next(self: RangeIterator[t]) Option[t] / exn:
        if self.current >= self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.step()
            Option.Some(current)

    size(self: RangeIterator[t]) Option[U32]:
        self.current.stepsBetween(self.end)


impl[Clone[t]] Clone[RangeIterator[t]]:
    clone(self: RangeIterator[t]) RangeIterator[t]:
        RangeIterator(current = self.current.clone(), end = self.end.clone())


# --------------------------------------------------------------------------------------------------


type InclusiveRangeIterator[t](
    current: t,
    end: t,
)


impl[Step[t], Ord[t]] Iterator[InclusiveRangeIterator[t], t, exn]:
    next(self: InclusiveRangeIterator[t]) Option[t] / exn:
        if self.current > self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.step()
            Option.Some(current)


impl[Clone[t]] Clone[InclusiveRangeIterator[t]]:
    clone(self: InclusiveRangeIterator[t]) InclusiveRangeIterator[t]:
        InclusiveRangeIterator(
            current = self.current.clone(),
            end = self.end.clone(),
        )


# --------------------------------------------------------------------------------------------------


type Map[iter, a, b, exn](
    iter: iter,
    f: Fn(a) b / exn,
)


impl[Iterator[iter, a, exn]] Iterator[Map[iter, a, b, exn], b, exn]:
    next(self: Map[iter, a, b, exn]) Option[b] / exn:
        match self.iter.next():
            Option.None: Option.None
            Option.Some(a): Option.Some(self.f(a))

    size(self: Map[iter, a, b, exn]) Option[U32] / exn2:
        self.iter.size[iter, a, exn, exn2]()


# --------------------------------------------------------------------------------------------------


type Peekable[iter, item, exn](
    iter: iter,
    peeked: Option[item],
)


impl[Iterator[iter, item, exn]] Iterator[Peekable[iter, item, exn], item, exn]:
    next(self: Peekable[iter, item, exn]) Option[item] / exn:
        match self.peeked:
            Option.Some(peeked):
                self.peeked = Option.None
                Option.Some(peeked)
            Option.None: self.iter.next()

    size(self: Peekable[iter, item, exn]) Option[U32] / exn2:
        self.iter.size[iter, item, exn, exn2]()


Peekable.peek[Iterator[iter, item, exn]](self: Peekable[iter, item, exn]) Option[item] / exn:
    match self.peeked:
        Option.Some(peeked): Option.Some(peeked)
        Option.None:
            self.peeked = self.iter.next()
            self.peeked


impl[Clone[iter], Clone[item]] Clone[Peekable[iter, item, exn]]:
    clone(self: Peekable[iter, item, exn]) Peekable[iter, item, exn]:
        Peekable(iter = self.iter.clone(), peeked = self.peeked.clone())


# --------------------------------------------------------------------------------------------------


type MapResult[iter, item, b, exnOld, exnNew](
    iter: iter,
    f: Fn(Result[exnOld, Option[item]]) Option[b] / exnNew,
)


impl[Iterator[iter, item, exnOld]] Iterator[MapResult[iter, item, b1, exnOld, exnNew], b1, exnNew]:
    next(self: MapResult[iter, item, b1, exnOld, exnNew]) Option[b1] / exnNew:
        self.f(try(self.iter.next))

    size(self: MapResult[iter, item, b1, exnOld, exnNew]) Option[U32] / exn3:
        self.iter.size[iter, item, exnOld, exn3]()


# --------------------------------------------------------------------------------------------------


type Try[iter, item, exn](
    iter: iter,
)


impl[Iterator[iter, item, exn]] Iterator[Try[iter, item, exn], Result[exn, item], exn2]:
    next(self: Try[iter, item, exn]) Option[Result[exn, item]] / exn2:
        match try(self.iter.next):
            Result.Err(err): Option.Some(Result.Err(err))
            Result.Ok(Option.Some(item)): Option.Some(Result.Ok(item))
            Result.Ok(Option.None): Option.None

    size(self: Try[iter, item, exn]) Option[U32] / exn3:
        self.iter.size[iter, item, exn, exn3]()


impl[Clone[iter]] Clone[Try[iter, item, exn]]:
    clone(self: Try[iter, item, exn]) Try[iter, item, exn]:
        Try(iter = self.iter.clone())


# --------------------------------------------------------------------------------------------------


type Skip[iter, item, exn](
    iter: iter,
    amount: U32,
)


impl[Iterator[iter, item, exn]] Iterator[Skip[iter, item, exn], item, exn]:
    next(self: Skip[iter, item, exn]) Option[item] / exn:
        while self.amount != 0:
            let _: Option[item] = self.iter.next()
            self.amount -= 1
        self.iter.next()

    size(self: Skip[iter, item, exn]) Option[U32] / exn2:
        if self.iter.size[iter, item, exn, exn2]() is Option.Some(size):
            return Option.Some(size - self.amount)
        Option.None


impl[Clone[iter]] Clone[Skip[iter, item, exn]]:
    clone(self: Skip[iter, item, exn]) Skip[iter, item, exn]:
        Skip(iter = self.iter.clone(), amount = self.amount)


# --------------------------------------------------------------------------------------------------


type Once[t](
    val: Option[t],
)


once(val: t) Once[t]:
    Once(val = Option.Some(val))


impl Iterator[Once[t], t, exn]:
    next(self: Once[t]) Option[t] / exn:
        let val = self.val
        self.val = Option.None
        val

    size(self: Once[t]) Option[U32]:
        Option.Some(1)


impl[Clone[t]] Clone[Once[t]]:
    clone(self: Once[t]) Once[t]:
        Once(val = self.val.clone())


# --------------------------------------------------------------------------------------------------

type OnceWith[t, exn](
    f: Option[Fn() t / exn],
)


onceWith(f: Fn() t / exn) OnceWith[t, exn]:
    OnceWith(f = Option.Some(f))


impl Iterator[OnceWith[t, exn], t, exn]:
    next(self: OnceWith[t, exn]) Option[t] / exn:
        match self.f:
            Option.None: Option.None
            Option.Some(f):
                self.f = Option.None
                Option.Some(f())

    size(self: OnceWith[t, exn]) Option[U32]:
        Option.Some(1)


# --------------------------------------------------------------------------------------------------


type Empty


empty() Empty:
    Empty


impl Iterator[Empty, item, exn]:
    next(self: Empty) Option[item] / exn:
        Option.None

    size(self: Empty) Option[U32]:
        Option.Some(0)


impl Clone[Empty]:
    clone(self: Empty) Empty:
        Empty


# --------------------------------------------------------------------------------------------------


type Chain[iter1, iter2, item, exn](
    iter1: Option[iter1],
    iter2: Option[iter2],
)


impl[Iterator[iter1, item, exn], Iterator[iter2, item, exn]] Iterator[Chain[iter1, iter2, item, exn], item, exn]:
    next(self: Chain[iter1, iter2, item, exn]) Option[item] / exn:
        if self.iter1 is Option.Some(iter1):
            match iter1.next():
                Option.Some(val): return Option.Some(val)
                Option.None: self.iter1 = Option.None

        if self.iter2 is Option.Some(iter2):
            match iter2.next():
                Option.Some(val): return Option.Some(val)
                Option.None: self.iter2 = Option.None

        Option.None

    size(self: Chain[iter1, iter2, item, exn]) Option[U32] / exn2:
        let hint: U32 = 0

        if self.iter1 is Option.Some(iter):
            match iter.size[iter1, item, exn, exn2]():
                Option.None: return Option.None
                Option.Some(hint_): hint += hint_

        if self.iter2 is Option.Some(iter):
            match iter.size[iter2, item, exn, exn2]():
                Option.None: return Option.None
                Option.Some(hint_): hint += hint_

        Option.Some(hint)


impl[Clone[iter1], Clone[iter2]] Clone[Chain[iter1, iter2, item, exn]]:
    clone(self: Chain[iter1, iter2, item, exn]) Chain[iter1, iter2, item, exn]:
        Chain(iter1 = self.iter1.clone(), iter2 = self.iter2.clone())


# --------------------------------------------------------------------------------------------------


type Filter[iter, item, exn](
    iter: iter,
    f: Fn(item) Bool / exn,
)


impl[Iterator[iter, item, exn]] Iterator[Filter[iter, item, exn], item, exn]:
    next(self: Filter[iter, item, exn]) Option[item] / exn:
        while self.iter.next() is Option.Some(item):
            if self.f(item):
                return Option.Some(item)

        Option.None


# --------------------------------------------------------------------------------------------------


type Enumerate[iter, item, exn](
    iter: iter,
    idx: U32,
)


# TODO: Maybe update item type to `(U32, item)` once we have records with positional fields.
impl[Iterator[iter, item, exn]] Iterator[Enumerate[iter, item, exn], (idx: U32, item: item), exn]:
    next(self: Enumerate[iter, item, exn]) Option[(idx: U32, item: item)] / exn:
        match self.iter.next():
            Option.None: Option.None
            Option.Some(item):
                let idx = self.idx
                self.idx += 1
                Option.Some((idx = idx, item = item))

    size(self: Enumerate[iter, item, exn]) Option[U32] / exn2:
        self.iter.size[iter, item, exn, exn2]()


impl[Clone[iter]] Clone[Enumerate[iter, item, exn]]:
    clone(self: Enumerate[iter, item, exn]) Enumerate[iter, item, exn]:
        Enumerate(iter = self.iter.clone(), idx = self.idx)


# --------------------------------------------------------------------------------------------------


type RepeatWith[item, exn](
    f: Fn() item / exn,
)


repeatWith(f: Fn() item / exn) RepeatWith[item, exn]:
    RepeatWith(f)


impl Iterator[RepeatWith[item, exn], item, exn]:
    next(self: RepeatWith[item, exn]) Option[item] / exn:
        Option.Some(self.f())


# --------------------------------------------------------------------------------------------------


type Take[iter, item, exn](
    iter: iter,
    n: U32,
)


impl[Iterator[iter, item, exn]] Iterator[Take[iter, item, exn], item, exn]:
    next(self: Take[iter, item, exn]) Option[item] / exn:
        if self.n == 0:
            Option.None
        else:
            self.n -= 1
            self.iter.next()

    size(self: Take[iter, item, exn]) Option[U32] / exn2:
        self.iter.size[iter, item, exn, exn2]().map(
            \(size: U32):
                if size >= self.n:
                    self.n
                else:
                    size,
        )
