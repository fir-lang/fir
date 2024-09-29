type Vec[T]:
    data: Array[T]
    len: U32

impl[T] Vec[T]:
    fn withCapacity(cap: U32): Vec[T] =
        Vec(data = Array.new(cap), len = 0)

    fn len(self): U32 =
        self.len

    fn clear(self) =
        # In the compiled version we should actually clear the elements to allow garbage collection.
        self.len = 0

    fn push(self, elem: T) =
        let cap = self.data.len()

        if self.len == cap:
            let newData = Array.new(cap * 2)
            for i in 0u32 .. cap:
                newData.set(i, self.data.get(i))
            self.data = newData

        self.data.set(self.len, elem)
        self.len += 1

    fn pop(self): Option[T] =
        if self.len == 0:
            return Option.None

        self.len -= 1
        Option.Some(self.data.get(self.len))

    fn set(self, idx: U32, elem: T) =
        if idx >= self.len:
            panic("Vec.set OOB (len=`self.len.toStr()`, idx=`idx.toStr()`)")

        self.data.set(idx, elem)

    fn get(self, idx: U32): T =
        if idx >= self.len:
            panic("Vec.get OOB (len=`self.len.toStr()`, idx=`idx.toStr()`)")

        self.data.get(idx)
