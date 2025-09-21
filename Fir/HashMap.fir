type HashMap[k, v](
    _elems: Vec[Option[Elem[k, v]]],
)


type Elem[k, v](
    key: k,
    value: v,
    next: Option[Elem[k, v]],
)


HashMap.withCapacity(cap: U32) HashMap[k, v]:
    let elems: Vec[Option[Elem[k, v]]] = Vec.withCapacity(cap)
    for i: U32 in range(u32(0), cap):
        elems.push(Option.None)
    HashMap(_elems = elems)


HashMap.fromIter[Iterator[iter, (key: k, value: v), exn], Eq[k], Hash[k]](
    iter: iter,
) HashMap[k, v] / exn:
    let map = HashMap.withCapacity(10)
    for item: (key: k, value: v) in iter:
        map.insert(item.key, item.value)
    map


HashMap.iter(self: HashMap[k, v]) HashMapIter[k, v]:
    HashMapIter.new(self)


# Insert new value, return old value.
HashMap.insert[Hash[k], Eq[k]](self: HashMap[k, v], key: k, value: v) Option[v]:
    let hash = key.hash()
    let index = hash.mod(self._elems.len())
    match self._elems.get(index):
        Option.None:
            self._elems.set(
                index,
                Option.Some(Elem(key = key, value = value, next = Option.None)),
            )
            return Option.None
        Option.Some(elem):
            loop:
                if elem.key == key:
                    let old = elem.value
                    elem.value = value
                    return Option.Some(old)
                else:
                    match elem.next:
                        Option.Some(next): elem = next
                        Option.None:
                            elem.next = Option.Some(
                                Elem(
                                    key = key,
                                    value = value,
                                    next = Option.None,
                                ),
                            )
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
        for entry: HashMapEntry[k, v] in self.iter():
            if printed != 0:
                buf.pushStr(", ")
            buf.pushStr(entry.key.toStr())
            buf.pushStr(": ")
            buf.pushStr(entry.value.toStr())
            printed += 1
        buf.push('}')
        buf.toStr()


impl[ToDoc[k], ToDoc[v]] ToDoc[HashMap[k, v]]:
    toDoc(self: HashMap[k, v]) Doc:
        let elems = Doc.empty()
        let printed: U32 = 0
        for entry: HashMapEntry[k, v] in self.iter():
            if printed != 0:
                elems += Doc.char(',') + Doc.break_(1)
            elems += Doc.grouped(
                entry.key.toDoc()
                    + Doc.blank(1)
                    + Doc.char('=')
                    + Doc.break_(1)
                    + entry.value.toDoc(),
            )
            printed += 1

        if printed != 0:
            elems += Doc.whenNotFlat(Doc.char(','))

        Doc.grouped(
            Doc.char('{')
                + Doc.nested(4, Doc.break_(0) + elems)
                + Doc.break_(0)
                + Doc.char('}'),
        )


type HashMapIter[k, v](
    _elems: Vec[Option[Elem[k, v]]],

    # Current index in `_elems`.
    _idx: U32,

    # Current element to yield.
    _nextElem: Option[Elem[k, v]],
)


type HashMapEntry[k, v](
    key: k,
    value: v,
)


HashMapIter.new(map: HashMap[k, v]) HashMapIter[k, v]:
    HashMapIter(
        _elems = map._elems,
        _idx = 0,
        _nextElem = map._elems.getOpt(0).flatten(),
    )


impl Iterator[HashMapIter[k, v], HashMapEntry[k, v], exn]:
    next(self: HashMapIter[k, v]) Option[HashMapEntry[k, v]] / exn:
        match self._nextElem:
            Option.Some(next):
                let ret = HashMapEntry(key = next.key, value = next.value)
                self._nextElem = next.next
                Option.Some(ret)

            Option.None:
                while self._idx + 1 < self._elems.len():
                    self._idx += 1
                    self._nextElem = self._elems.get(self._idx)
                    if self._nextElem is Option.Some(_):
                        return self.next()

                Option.None
