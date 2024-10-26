type Vec[T]:
    _data: Array[T]
    _len: U32

impl[T] Vec[T]:
    fn withCapacity(cap: U32): Vec[T] =
        Vec(_data = Array.new(cap), _len = 0)

    fn len(self): U32 =
        self._len

    fn clear(self) =
        # In the compiled version we should actually clear the elements to allow garbage collection.
        self._len = 0

    fn push(self, elem: T) =
        let cap = self._data.len()

        if self._len == cap:
            let newData = Array.new(cap * 2)
            for i in range(0u32, cap):
                newData.set(i, self._data.get(i))
            self._data = newData

        self._data.set(self._len, elem)
        self._len += 1

    fn pop(self): Option[T] =
        if self._len == 0:
            return Option.None

        self._len -= 1
        Option.Some(self._data.get(self._len))

    fn set(self, idx: U32, elem: T) =
        if idx >= self._len:
            panic("Vec.set OOB (len=`self._len.toStr()`, idx=`idx.toStr()`)")

        self._data.set(idx, elem)

    fn get(self, idx: U32): T =
        if idx >= self._len:
            panic("Vec.get OOB (len=`self._len.toStr()`, idx=`idx.toStr()`)")

        self._data.get(idx)
