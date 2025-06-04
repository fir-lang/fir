prim type Array[t]

prim Array.new(len: U32) Array[t]
prim Array.len(self: Array[t]) U32
prim Array.get(self: Array[t], idx: U32) t
prim Array.set(self: Array[t], idx: U32, elem: t)

Array.fromIter[Iterator[iter, item, exn]](iter: iter) Array[item] / exn:
    let size = match iter.size[iter, item, exn, exn]():
        Option.Some(size): size
        Option.None: panic("Array.fromIter iterator size unknown")

    let array = Array.new(size)

    for i: U32 in range(0u32, size):
        array.set(i, iter.next().unwrap())

    array

impl[ToStr[t]] ToStr[Array[t]]:
    toStr(self: Array[t]) Str:
        let buf = StrBuf.withCapacity(self.len() * 5 + 2)
        buf.push('[')
        for i: U32 in range(0u32, self.len()):
            if i != 0:
                buf.push(',')
            buf.pushStr(self.get(i).toStr())
        buf.push(']')
        buf.toStr()
