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

    ## Count number of elements the iterator yields.
    ##
    ## Note that this consumes the iterator. The iterator won't yield any more elements after
    ## calling this method.
    ##
    ## See also `size` for a version of this that returns the number of elements without consuming
    ## the iterator.
    count(self: iter) U32 / exn:
        let n = 0u32
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

# --------------------------------------------------------------------------------------------------

trait Step[t]:
    step(self: t) t

range(start: t, end: t) RangeIterator[t]:
    RangeIterator(current = start, end = end)

irange(start: t, end: t) InclusiveRangeIterator[t]:
    InclusiveRangeIterator(current = start, end = end)

type RangeIterator[t]:
    current: t
    end: t

impl[Step[t], Ord[t]] Iterator[RangeIterator[t], t, exn]:
    next(self: RangeIterator[t]) Option[t] / exn:
        if self.current >= self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.step()
            Option.Some(current)

# --------------------------------------------------------------------------------------------------

type InclusiveRangeIterator[t]:
    current: t
    end: t

impl[Step[t], Ord[t]] Iterator[InclusiveRangeIterator[t], t, exn]:
    next(self: InclusiveRangeIterator[t]) Option[t] / exn:
        if self.current > self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.step()
            Option.Some(current)

# --------------------------------------------------------------------------------------------------

# NOTE: The row type parameter needs to start with `recRow` to have kind `row(variant)`.
type Map[iter, a, b, exn]:
    iter: iter
    f: Fn(a) b / exn

# BUG(#86): To work around substitution bugs, give quantified variables
# different names than the quantified variables of `Iterator`.
impl[Iterator[iter1, a1, exn1]] Iterator[Map[iter1, a1, b1, exn1], b1, exn1]:
    next(self: Map[iter1, a1, b1, exn1]) Option[b1] / exn1:
        match self.iter.next():
            Option.None: Option.None
            Option.Some(a): Option.Some(self.f(a))

    size(self: Map[iter1, a1, b1, exn1]) Option[U32] / exn2:
        self.iter.size[iter1, a1, exn1, exn2]()

# --------------------------------------------------------------------------------------------------

type Peekable[iter, item, exn]:
    iter: iter
    peeked: Option[item]

impl[Iterator[iter, item, exn]] Iterator[Peekable[iter, item, exn], item, exn]:
    next(self: Peekable[iter, item, exn]) Option[item] / exn:
        match self.peeked:
            Option.Some(peeked):
                self.peeked = Option.None
                Option.Some(peeked)
            Option.None:
                self.iter.next()

    size(self: Peekable[iter, item, exn]) Option[U32] / exn2:
        self.iter.size[iter, item, exn, exn2]()

Peekable.peek[Iterator[iter, item, exn]](self: Peekable[iter, item, exn]) Option[item] / exn:
    match self.peeked:
        Option.Some(peeked):
            Option.Some(peeked)
        Option.None:
            self.peeked = self.iter.next()
            self.peeked

# --------------------------------------------------------------------------------------------------

type MapResult[iter, item, b, exnOld, exnNew]:
    iter: iter
    f: Fn(Result[exnOld, Option[item]]) Option[b] / exnNew

impl[Iterator[iter1, item1, exnOld1]] Iterator[MapResult[iter1, item1, b1, exnOld1, exnNew1], b1, exnNew1]:
    next(self: MapResult[iter1, item1, b1, exnOld1, exnNew1]) Option[b1] / exnNew1:
        self.f(try(self.iter.next))

    size(self: MapResult[iter1, item1, b1, exnOld1, exnNew1]) Option[U32] / exn3:
        self.iter.size[iter1, item1, exnOld1, exn3]()

# --------------------------------------------------------------------------------------------------

type Try[iter, item, exn]:
    iter: iter

impl[Iterator[iter1, item1, exn1]] Iterator[Try[iter1, item1, exn1], Result[exn1, item1], exn2]:
    next(self: Try[iter1, item1, exn1]) Option[Result[exn1, item1]] / exn2:
        match try(self.iter.next):
            Result.Err(err): Option.Some(Result.Err(err))
            Result.Ok(Option.Some(item)): Option.Some(Result.Ok(item))
            Result.Ok(Option.None): Option.None

    size(self: Try[iter1, item1, exn1]) Option[U32] / exn3:
        self.iter.size[iter1, item1, exn1, exn3]()

# --------------------------------------------------------------------------------------------------

type Skip[iter, item, exn]:
    iter: iter
    amount: U32

impl[Iterator[iter1, item1, exn1]] Iterator[Skip[iter1, item1, exn1], item1, exn1]:
    next(self: Skip[iter1, item1, exn1]) Option[item1] / exn1:
        while self.amount != 0:
            let _: Option[item1] = self.iter.next()
            self.amount -= 1
        self.iter.next()

    size(self: Skip[iter1, item1, exn1]) Option[U32] / exn2:
        if self.iter.size[iter1, item1, exn1, exn2]() is Option.Some(size):
            return Option.Some(size - self.amount)
        Option.None

# --------------------------------------------------------------------------------------------------

type Once[t]:
    val: Option[t]

once(val: t) Once[t]:
    Once(val = Option.Some(val))

impl Iterator[Once[t], t, exn]:
    next(self: Once[t]) Option[t] / exn:
        let val = self.val
        self.val = Option.None
        val

    size(self: Once[t]) Option[U32]:
        Option.Some(1)

# --------------------------------------------------------------------------------------------------

type OnceWith[t, exn]:
    f: Option[Fn() t / exn]

onceWith(f: Fn() t / exn) OnceWith[t, exn]:
    OnceWith(f = Option.Some(f))

impl Iterator[OnceWith[t, exn], t, exn]:
    next(self: OnceWith[t, exn]) Option[t] / exn:
        match self.f:
            Option.None:
                Option.None
            Option.Some(f):
                self.f = Option.None
                Option.Some(f())

    size(self: OnceWith[t, exn]) Option[U32]:
        Option.Some(1)

# --------------------------------------------------------------------------------------------------

# TODO: We don't have a syntax to declare unit types.
type Empty:
    x: ()

empty() Empty:
    Empty(x = ())

impl Iterator[Empty, item, exn]:
    next(self: Empty) Option[item] / exn:
        Option.None

    size(self: Empty) Option[U32]:
        Option.Some(0)

# --------------------------------------------------------------------------------------------------

type Chain[iter1, iter2, item, exn]:
    iter1: Option[iter1]
    iter2: Option[iter2]

impl[Iterator[iter1, item, exn], Iterator[iter2, item, exn]] Iterator[Chain[iter1, iter2, item, exn], item, exn]:
    next(self: Chain[iter1, iter2, item, exn]) Option[item] / exn:
        if self.iter1 is Option.Some(iter1):
            match iter1.next():
                Option.Some(val):
                    return Option.Some(val)
                Option.None:
                    self.iter1 = Option.None

        if self.iter2 is Option.Some(iter2):
            match iter2.next():
                Option.Some(val):
                    return Option.Some(val)
                Option.None:
                    self.iter2 = Option.None

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
