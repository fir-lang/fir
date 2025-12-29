prim type Array[t]


prim Array.new(len: U32) Array[t]


prim Array.len(self: Array[t]) U32


prim Array.get(self: Array[t], idx: U32) t


prim Array.set(self: Array[t], idx: U32, elem: t)


prim Array.slice(self: Array[t], start: U32, end: U32) Array[t]


# memmove
prim Array.copyWithin(self: Array[t], src: U32, dst: U32, len: U32)


Array.getOpt(self: Array[t], idx: U32) Option[t]:
    if idx < self.len():
        Option.Some(self.get(idx))
    else:
        Option.None


## Create an array of length `size`, from the iterator `iter`.
##
## The iterator should yield at least `size` amount of times, to be able to
## initialize the array elements.
Array.fromIter[Iterator[iter, item, exn]](iter: iter, size: U32) Array[item] / exn:
    let array = Array.new(size)

    for i: U32 in range(u32(0), size):
        array.set(i, iter.next().unwrap())

    array


Array.iter(self: Array[t]) ArrayIter[t]:
    ArrayIter(_array = self, _idx = 0)


## Reverse the order of elements, in place.
Array.reverse(self: Array[t]):
    self.reverseRange(0, self.len())


## Reverse the slice of the array from start to end (exclusive), in place.
Array.reverseRange(self: Array[t], start: U32, end: U32):
    if start >= end:
        return

    for i in range(u32(0), (end - start) / 2):
        let tmp = self.get(start + i)
        self.set(start + i, self.get(end - 1 - i))
        self.set(end - 1 - i, tmp)


impl[Clone[t]] Clone[Array[t]]:
    clone(self: Array[t]) Array[t]:
        let new = Array.new(self.len())
        for i: U32 in range(u32(0), self.len()):
            new.set(i, self.get(i))
        new


impl[ToStr[t]] ToStr[Array[t]]:
    toStr(self: Array[t]) Str:
        let buf = StrBuf.withCapacity(self.len() * 5 + 2)
        buf.push('[')
        for i: U32 in range(u32(0), self.len()):
            if i != 0:
                buf.push(',')
            buf.pushStr(self.get(i).toStr())
        buf.push(']')
        buf.toStr()


impl[ToDoc[t]] ToDoc[Array[t]]:
    toDoc(self: Array[t]) Doc:
        if self.len() == 0:
            return Doc.str("Array.[]")

        let args = Doc.empty()
        for i: U32 in range(u32(0), self.len()):
            if i != 0:
                args += Doc.char(',') + Doc.break_(1)
            args += self.get(i).toDoc()
        Doc.grouped(
            Doc.str("Array.[")
                + Doc.nested(4, Doc.break_(0) + args).group()
                + Doc.break_(0)
                + Doc.char(']'),
        )


type ArrayIter[t](
    _array: Array[t],
    _idx: U32,
)


impl Iterator[ArrayIter[t], t, exn]:
    next(self: ArrayIter[t]) Option[t] / exn:
        if self._idx >= self._array.len():
            return Option.None

        let val = self._array.get(self._idx)
        self._idx += 1
        Option.Some(val)
