type Deque[t](
    _data: Array[t],
    _head: U32,
    _len: U32,
)


Deque.withCapacity(cap: U32) Deque[t]:
    Deque(_data = Array.new(cap), _head = 0, _len = 0)


Deque.empty() Deque[t]:
    Deque.withCapacity(0)


Deque.fromIter[Iterator[iter, item, exn]](iter: iter) Deque[item] / exn:
    let size = iter.size[iter, item, exn, exn]().unwrapOr(10)
    let deque = Deque.withCapacity(size)
    for item: item in iter:
        deque.pushBack(item)
    deque


Deque.iter(self: Deque[t]) DequeIter[t]:
    DequeIter(_deque = self, _idx = 0)


Deque.get(self: Deque[t], idx: U32) t:
    if idx >= self._len:
        panic("Deque.get OOB (len=`self._len`, idx=`idx`)")

    self._data.get((self._head + idx).rem(self._data.len()))


Deque.reserve(self: Deque[t], additional: U32):
    if additional == 0:
        return
    let len = self.len()
    let newCap = max(u32(8), (len + additional).nextPowerOfTwo())
    if newCap > self._data.len():
        let newData = Array.new(newCap)
        let oldHead = self._head
        for i: U32 in range(u32(0), len):
            newData.set(i, self._data.get((oldHead + i).rem(len)))
        self._data = newData
        self._head = 0


Deque.len(self: Deque[t]) U32:
    self._len


Deque.isEmpty(self: Deque[t]) Bool:
    self._len == 0


Deque.pushBack(self: Deque[t], item: t):
    self.reserve(1)
    self._data.set((self._head + self._len).rem(self._data.len()), item)
    self._len += 1


Deque.pushFront(self: Deque[t], item: t):
    self.reserve(1)
    if self._head == 0:
        self._head = self._data.len() - 1
    else:
        self._head -= 1
    self._len += 1
    self._data.set(self._head, item)


Deque.popBack(self: Deque[t]) Option[t]:
    if self._len == 0:
        return Option.None

    self._len -= 1
    Option.Some(self._data.get((self._head + self._len).rem(self._data.len())))


Deque.popFront(self: Deque[t]) Option[t]:
    if self._len == 0:
        return Option.None

    self._len -= 1
    let elem = self._data.get(self._head)
    self._head = (self._head + 1).rem(self._data.len())
    Option.Some(elem)


impl[ToStr[t]] ToStr[Deque[t]]:
    toStr(self: Deque[t]) Str:
        let buf = StrBuf.withCapacity(self.len() * 5 + 2)
        buf.push('[')
        for i: U32 in range(u32(0), self.len()):
            if i != 0:
                buf.push(',')
            buf.pushStr(self.get(i).toStr())
        buf.push(']')
        buf.toStr()


impl[ToDoc[t]] ToDoc[Deque[t]]:
    toDoc(self: Deque[t]) Doc:
        if self.isEmpty():
            return Doc.str("Deque.[]")

        let args = Doc.empty()
        for i: U32 in range(u32(0), self.len()):
            if i != 0:
                args += Doc.char(',') + Doc.break_(1)
            args += self.get(i).toDoc()
        Doc.grouped(
            Doc.str("Deque.[")
                + Doc.nested(4, Doc.break_(0) + args).group()
                + Doc.break_(0)
                + Doc.char(']'),
        )


impl[Eq[t]] Eq[Deque[t]]:
    __eq(self: Deque[t], other: Deque[t]) Bool:
        if self.len() != other.len():
            return Bool.False

        for i: U32 in range(u32(0), self.len()):
            if self.get(i) != other.get(i):
                return Bool.False

        Bool.True


impl[Hash[t]] Hash[Deque[t]]:
    hash(self: Deque[t]) U32:
        let hash = self.len()
        for t: t in self.iter():
            hash += t.hash()
        hash


type DequeIter[t](
    _deque: Deque[t],
    _idx: U32,
)


impl Iterator[DequeIter[t], t, exn]:
    next(self: DequeIter[t]) Option[t] / exn:
        if self._idx >= self._deque.len():
            return Option.None

        let val = self._deque.get(self._idx)
        self._idx += 1
        Option.Some(val)


impl[Clone[t]] Clone[Deque[t]]:
    clone(self: Deque[t]) Deque[t]:
        let ret: Deque[t] = Deque.withCapacity(self.len())
        for t: t in self.iter():
            ret.pushBack(t.clone())
        ret
