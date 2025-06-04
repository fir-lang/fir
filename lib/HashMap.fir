type HashMap[k, v]:
    _elems: Vec[Option[Elem[k, v]]]

type Elem[k, v]:
    key: k
    value: v
    next: Option[Elem[k, v]]

HashMap.fromIter[Iterator[iter, (key: k, value: v), exn], Eq[k], Hash[k]](iter: iter) HashMap[k, v] / exn:
    let map = HashMap.withCapacity(10)
    for item: (key: k, value: v) in iter:
        map.insert(item.key, item.value)
    map

HashMap.withCapacity(cap: U32) HashMap[k, v]:
    let elems: Vec[Option[Elem[k, v]]] = Vec.withCapacity(cap)
    for i: U32 in range(0u32, cap):
        elems.push(Option.None)
    HashMap(_elems = elems)

# Insert new value, return old value.
HashMap.insert[Hash[k], Eq[k]](self: HashMap[k, v], key: k, value: v) Option[v]:
    let hash = key.hash()
    let index = hash.mod(self._elems.len())
    match self._elems.get(index):
        Option.None:
            self._elems.set(index, Option.Some(Elem(key = key, value = value, next = Option.None)))
            return Option.None
        Option.Some(elem):
            loop:
                if elem.key == key:
                    let old = elem.value
                    elem.value = value
                    return Option.Some(old)
                else:
                    match elem.next:
                        Option.Some(next):
                            elem = next
                        Option.None:
                            elem.next = Option.Some(Elem(key = key, value = value, next = Option.None))
                            return Option.None

    panic("unreachable")

HashMap.get[Hash[k], Eq[k]](self: HashMap[k, v], key: k) Option[v]:
    let hash = key.hash()
    let index = hash.mod(self._elems.len())
    let elem = self._elems.get(index)
    loop:
        match elem:
            Option.None: return Option.None
            Option.Some(elem_):
                if elem_.key == key:
                    return Option.Some(elem_.value)
                else:
                    elem = elem_.next

    panic("unreachable")

impl[ToStr[k], ToStr[v]] ToStr[HashMap[k, v]]:
    toStr(self: HashMap[k, v]) Str:
        let buf = StrBuf.withCapacity(100)
        buf.push('{')
        let printed = 0
        for i: U32 in range(0u32, self._elems.len()):
            let elem = self._elems.get(i)
            while elem is Option.Some(elem_):
                if printed != 0:
                    buf.pushStr(", ")
                buf.pushStr(elem_.key.toStr())
                buf.pushStr(": ")
                buf.pushStr(elem_.value.toStr())
                printed += 1
                elem = elem_.next
        buf.push('}')
        buf.toStr()
