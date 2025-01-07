type Vec[t]:
    _data: Array[t]
    _len: U32

impl[t] Vec[t]:
    fn withCapacity(cap: U32): Vec[t]
        Vec(_data = Array.new(cap), _len = 0)

    fn reserve(self, cap: U32)
        let len = self._len
        let newCap = self._data.len()
        while newCap - len < cap:
            newCap *= 2

        if newCap != self._data.len():
            let newData = Array.new(newCap)
            for i in range(0u32, self._data.len()):
                newData.set(i, self._data.get(i))
            self._data = newData

    fn spareCapacity(self): U32
        self._data.len() - self._len

    fn len(self): U32
        self._len

    fn clear(self)
        # In the compiled version we should actually clear the elements to allow garbage collection.
        self._len = 0

    fn push(self, elem: t)
        let cap = self._data.len()

        if self._len == cap:
            let newData = Array.new(cap * 2)
            for i in range(0u32, cap):
                newData.set(i, self._data.get(i))
            self._data = newData

        self._data.set(self._len, elem)
        self._len += 1

    fn pop(self): Option[t]
        if self._len == 0:
            return Option.None

        self._len -= 1
        Option.Some(self._data.get(self._len))

    fn set(self, idx: U32, elem: t)
        if idx >= self._len:
            panic("Vec.set OOB (len=`self._len.toStr()`, idx=`idx.toStr()`)")

        self._data.set(idx, elem)

    fn get(self, idx: U32): t
        if idx >= self._len:
            panic("Vec.get OOB (len=`self._len.toStr()`, idx=`idx.toStr()`)")

        self._data.get(idx)

    fn swap(self, i: U32, j: U32)
        let tmp = self.get(i)
        self.set(i, self.get(j))
        self.set(j, tmp)

impl[t: Ord] Vec[t]:
    fn sort(self)
        if self.len() != 0:
            _quicksort(self, 0, self.len() - 1)

fn _quicksort[t: Ord](vec: Vec[t], low: U32, high: U32)
    if low >= high:
        return ()   # TODO: Allow returning without a value

    let p = _partition(vec, low, high)

    if p != low:
        _quicksort(vec, low, p - 1)

    _quicksort(vec, p + 1, high)

fn _partition[t: Ord](vec: Vec[t], low: U32, high: U32): U32
    let pivot = vec.get(high)
    let i = low

    for j in irange(low, high - 1):
        if vec.get(j) <= pivot:
            vec.swap(i, j)
            i += 1

    vec.swap(i, high)
    i

impl[t: ToStr] ToStr for Vec[t]:
    fn toStr(self): Str
        let buf = StrBuf.withCapacity(self.len() * 5 + 2)
        buf.push('[')
        for i in range(0u32, self.len()):
            if i != 0:
                buf.push(',')
            buf.pushStr(self.get(i).toStr())
        buf.push(']')
        buf.toStr()
