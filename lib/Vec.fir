type Vec[t]:
    _data: Array[t]
    _len: U32

Vec.withCapacity(cap: U32): Vec[t]
    Vec(_data = Array.new(cap), _len = 0)

Vec.reserve(self: Vec[t], cap: U32)
    let len = self._len
    let newCap = self._data.len()
    while newCap - len < cap:
        newCap *= 2

    if newCap != self._data.len():
        let newData = Array.new(newCap)
        for i: U32 in range(0u32, self._data.len()):
            newData.set(i, self._data.get(i))
        self._data = newData

Vec.spareCapacity(self: Vec[t]): U32
    self._data.len() - self._len

Vec.len(self: Vec[t]): U32
    self._len

Vec.clear(self: Vec[t])
    # In the compiled version we should actually clear the elements to allow garbage collection.
    self._len = 0

Vec.push(self: Vec[t], elem: t)
    let cap = self._data.len()

    if self._len == cap:
        let newData = Array.new(cap * 2)
        for i: U32 in range(0u32, cap):
            newData.set(i, self._data.get(i))
        self._data = newData

    self._data.set(self._len, elem)
    self._len += 1

Vec.pop(self: Vec[t]): Option[t]
    if self._len == 0:
        return Option.None

    self._len -= 1
    Option.Some(self._data.get(self._len))

Vec.set(self: Vec[t], idx: U32, elem: t)
    if idx >= self._len:
        panic("Vec.set OOB (len=`self._len`, idx=`idx`)")

    self._data.set(idx, elem)

Vec.get(self: Vec[t], idx: U32): t
    if idx >= self._len:
        panic("Vec.get OOB (len=`self._len`, idx=`idx`)")

    self._data.get(idx)

Vec.swap(self: Vec[t], i: U32, j: U32)
    let tmp = self.get(i)
    self.set(i, self.get(j))
    self.set(j, tmp)

Vec.iter(self: Vec[t]): VecIter[t]
    VecIter(
        _vec = self,
        _idx = 0,
    )

Vec.first(self: Vec[t]): Option[t]
    if self.len() == 0:
        return Option.None
    Option.Some(self._data.get(0))

Vec.last(self: Vec[t]): Option[t]
    let len = self.len()
    if len == 0:
        return Option.None
    Option.Some(self._data.get(len - 1))

Vec.sort[Ord[t]](self: Vec[t])
    if self.len() != 0:
        _quicksort(self, 0, self.len() - 1)

_quicksort[Ord[t]](vec: Vec[t], low: U32, high: U32)
    if low >= high:
        return

    let p = _partition(vec, low, high)

    if p != low:
        _quicksort(vec, low, p - 1)

    _quicksort(vec, p + 1, high)

_partition[Ord[t]](vec: Vec[t], low: U32, high: U32): U32
    let pivot = vec.get(high)
    let i = low

    for j: U32 in irange(low, high - 1):
        if vec.get(j) <= pivot:
            vec.swap(i, j)
            i += 1

    vec.swap(i, high)
    i

impl[ToStr[t]] ToStr[Vec[t]]:
    toStr(self: Vec[t]): Str
        let buf = StrBuf.withCapacity(self.len() * 5 + 2)
        buf.push('[')
        for i: U32 in range(0u32, self.len()):
            if i != 0:
                buf.push(',')
            buf.pushStr(self.get(i).toStr())
        buf.push(']')
        buf.toStr()

type VecIter[t]:
    _vec: Vec[t]
    _idx: U32

impl Iterator[VecIter[t], t, exn]:
    next(self: VecIter[t]): exn Option[t]
        if self._idx >= self._vec.len():
            return Option.None

        let val = self._vec.get(self._idx)
        self._idx += 1
        Option.Some(val)
