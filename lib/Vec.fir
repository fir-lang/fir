type Vec[t](
    _data: Array[t],
    _len: U32,
)


Vec.empty() Vec[t]:
    Vec(_data = Array.new(0), _len = 0)


Vec.withCapacity(cap: U32) Vec[t]:
    Vec(_data = Array.new(cap), _len = 0)


Vec.fromIter[Iterator[iter, item, exn]](iter: iter) Vec[item] / exn:
    let size = iter.size[iter, item, exn, exn]().unwrapOr(10)
    let vec = Vec.withCapacity(size)
    for item: item in iter:
        vec.push(item)
    vec


Vec.reserve(self: Vec[t], cap: U32):
    let len = self._len
    let newCap = self._data.len()
    while newCap - len < cap:
        newCap *= 2

    if newCap != self._data.len():
        let newData = Array.new(newCap)
        for i: U32 in range(u32(0), self._data.len()):
            newData.set(i, self._data.get(i))
        self._data = newData


Vec.spareCapacity(self: Vec[t]) U32:
    self._data.len() - self._len


Vec.len(self: Vec[t]) U32:
    self._len


Vec.isEmpty(self: Vec[t]) Bool:
    self._len == 0


Vec.clear(self: Vec[t]):
    # In the compiled version we should actually clear the elements to allow garbage collection.
    self._len = 0


Vec.truncate(self: Vec[t], len: U32):
    if len < self._len:
        self._len = len


Vec.push(self: Vec[t], elem: t):
    let cap = self._data.len()

    if self._len == cap:
        let newData = Array.new((cap * 2) | 3)
        for i: U32 in range(u32(0), cap):
            newData.set(i, self._data.get(i))
        self._data = newData

    self._data.set(self._len, elem)
    self._len += 1


Vec.extend[Iterator[iter, t, exn]](self: Vec[t], iter: iter) / exn:
    if iter.size[iter, t, exn, exn]() is Option.Some(size):
        self.reserve(size)

    for item: t in iter:
        self.push(item)


Vec.insert(self: Vec[t], idx: U32, elem: t):
    if idx == self.len():
        self.push(elem)
        return

    self.reserve(1)
    self._data.copyWithin(idx, idx + 1, self.len() - idx)
    self._data.set(idx, elem)
    self._len += 1


Vec.remove(self: Vec[t], idx: U32) t:
    let len = self.len()

    if idx >= len:
        panic("Vec.remove OOB (len=`self._len`, idx=`idx`)")

    if idx + 1 == len:
        self._len -= 1
        return self._data.get(self._len)

    let elem = self._data.get(idx)
    self._data.copyWithin(idx + 1, idx, len - idx - 1)
    self._len -= 1
    elem


Vec.pop(self: Vec[t]) Option[t]:
    if self._len == 0:
        return Option.None

    self._len -= 1
    Option.Some(self._data.get(self._len))


Vec.set(self: Vec[t], idx: U32, elem: t):
    if idx >= self._len:
        panic("Vec.set OOB (len=`self._len`, idx=`idx`)")

    self._data.set(idx, elem)


Vec.get(self: Vec[t], idx: U32) t:
    if idx >= self._len:
        panic("Vec.get OOB (len=`self._len`, idx=`idx`)")

    self._data.get(idx)


Vec.getOpt(self: Vec[t], idx: U32) Option[t]:
    if idx >= self._len:
        return Option.None

    Option.Some(self._data.get(idx))


Vec.swap(self: Vec[t], i: U32, j: U32):
    let tmp = self.get(i)
    self.set(i, self.get(j))
    self.set(j, tmp)


Vec.iter(self: Vec[t]) VecIter[t]:
    VecIter(_vec = self, _idx = 0,)


Vec.first(self: Vec[t]) Option[t]:
    if self.len() == 0:
        return Option.None
    Option.Some(self._data.get(0))


Vec.last(self: Vec[t]) Option[t]:
    let len = self.len()
    if len == 0:
        return Option.None
    Option.Some(self._data.get(len - 1))


Vec.sort[Ord[t]](self: Vec[t]):
    if self.len() != 0:
        _quicksort(self, 0, self.len() - 1)


## Take the backing array of this `Vec`.
##
## The `Vec` will be reset: it'll have a new empty backing array and its length will be 0.
Vec.takeArray(self: Vec[t]) Array[t]:
    let array = self._data.slice(0, self._len)
    self._data = Array.new(0)
    self._len = 0
    array


_quicksort[Ord[t]](vec: Vec[t], low: U32, high: U32):
    if low >= high:
        return

    let p = _partition(vec, low, high)

    if p != low:
        _quicksort(vec, low, p - 1)

    _quicksort(vec, p + 1, high)


_partition[Ord[t]](vec: Vec[t], low: U32, high: U32) U32:
    let pivot = vec.get(high)
    let i = low

    for j: U32 in irange(low, high - 1):
        if vec.get(j) <= pivot:
            vec.swap(i, j)
            i += 1

    vec.swap(i, high)
    i


impl[ToStr[t]] ToStr[Vec[t]]:
    toStr(self: Vec[t]) Str:
        let buf = StrBuf.withCapacity(self.len() * 5 + 2)
        buf.push('[')
        for i: U32 in range(u32(0), self.len()):
            if i != 0:
                buf.push(',')
            buf.pushStr(self.get(i).toStr())
        buf.push(']')
        buf.toStr()


type VecIter[t](
    _vec: Vec[t],
    _idx: U32,
)


impl Iterator[VecIter[t], t, exn]:
    next(self: VecIter[t]) Option[t] / exn:
        if self._idx >= self._vec.len():
            return Option.None

        let val = self._vec.get(self._idx)
        self._idx += 1
        Option.Some(val)


impl Clone[VecIter[t]]:
    clone(self: VecIter[t]) VecIter[t]:
        VecIter(_vec = self._vec, _idx = self._idx)
