prim type Array[t]

prim Array.new(len: U32) Array[t]
prim Array.len(self: Array[t]) U32
prim Array.get(self: Array[t], idx: U32) t
prim Array.set(self: Array[t], idx: U32, elem: t)
prim Array.slice(self: Array[t], start: U32, end: U32) Array[t]

# memmove
prim Array.copyWithin(self: Array[t], src: U32, dst: U32, len: U32)

Array.fromIter[Iterator[iter, item, exn]](iter: iter) Array[item] / exn:
    let size = match iter.size[iter, item, exn, exn]():
        Option.Some(size): size
        Option.None: panic("Array.fromIter iterator size unknown")

    let array = Array.new(size)

    for i: U32 in range(u32(0), size):
        array.set(i, iter.next().unwrap())

    array

Array.iter(self: Array[t]) ArrayIter[t]:
    ArrayIter(
        _array = self,
        _idx = 0,
    )

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
