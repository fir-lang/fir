#[derive(ToDoc)]
type HashMap[k, v](
    _elems: Array[Option[Elem[k, v]]],

    ## How many more elements to add before growing the array and rehashing.
    _capacityLeft: U32,
)


#[derive(ToDoc)]
type Elem[k, v](
    key: k,
    value: v,
    next: Option[Elem[k, v]],
)


HashMap.empty() HashMap[k, v]:
    HashMap.withCapacity(0)


HashMap.withCapacity(cap: U32) HashMap[k, v]:
    let elems: Array[Option[Elem[k, v]]] = Array.fromIter(
        repeatWith(||: Option.None),
        cap,
    )
    HashMap(_elems = elems, _capacityLeft = HashMap._capacityBeforeGrowth(cap))


HashMap._capacityBeforeGrowth(cap: U32) U32:
    (u32(cap) * u32(8000)) / u32(10000)


HashMap.fromIter[Iterator[iter, (key: k, value: v), exn], Eq[k], Hash[k]](
    iter: iter,
) HashMap[k, v] / exn:
    let map = HashMap.withCapacity(10)
    for item: (key: k, value: v) in iter:
        map.insert(item.key, item.value)
    map


HashMap._grow[Eq[k], Hash[k]](self: HashMap[k, v]):
    let currentCap = self._elems.len()
    let newCap = if currentCap == 0:
        u32(10)
    else:
        currentCap * u32(2)

    let newElems: Array[Option[Elem[k, v]]] = Array.fromIter(
        repeatWith(||: Option.None),
        newCap,
    )

    let newCapacityLeft: U32 = HashMap._capacityBeforeGrowth(newCap)

    for entry: HashMapEntry[k, v] in self.iter():
        HashMap._insert(newElems, entry.key, entry.value)
        newCapacityLeft -= 1

    self._elems = newElems
    self._capacityLeft = newCapacityLeft


HashMap.fromEntries[Iterator[iter, HashMapEntry[k, v], exn], Eq[k], Hash[k]](
    iter: iter,
) HashMap[k, v] / exn:
    let map = HashMap.withCapacity(10)
    for item: HashMapEntry[k, v] in iter:
        map.insert(item.key, item.value)
    map


HashMap.iter(self: HashMap[k, v]) HashMapIter[k, v]:
    HashMapIter.new(self)


HashMap.keys(self: HashMap[k, v]) Map[HashMapIter[k, v], HashMapEntry[k, v], k, exn] / exn:
    HashMapIter.new(self).map(|entry: HashMapEntry[k, v]|: entry.key)


HashMap.values(self: HashMap[k, v]) Map[HashMapIter[k, v], HashMapEntry[k, v], v, exn] / exn:
    HashMapIter.new(self).map(|entry: HashMapEntry[k, v]|: entry.value)


# Insert new value, return old value.
HashMap.insert[Hash[k], Eq[k]](self: HashMap[k, v], key: k, value: v) Option[v]:
    if self._capacityLeft == 0:
        self._grow()

    let ret = HashMap._insert(self._elems, key, value)
    self._capacityLeft -= 1
    ret


HashMap._insert[Hash[k], Eq[k]](
    elems: Array[Option[Elem[k, v]]],
    key: k,
    value: v,
) Option[v]:
    let hash = key.hash()
    let index = hash.mod(elems.len())
    match elems.get(index):
        Option.None:
            elems.set(
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
            Doc.str("HashMap.[")
                + Doc.nested(4, Doc.break_(0) + elems)
                + Doc.break_(0)
                + Doc.char(']'),
        )


type HashMapIter[k, v](
    _elems: Array[Option[Elem[k, v]]],

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


# ------------------------------------------------------------------------------


HashMap.toDebugDoc[ToDoc[k], ToDoc[v]](self: HashMap[k, v]) Doc:
    let args = Doc.break_(0)
    args += Doc.grouped(
        Doc.str("_elems =") + Doc.nested(4, Doc.break_(1) + self._elems.toDoc()),
    )
    args += Doc.char(',') + Doc.break_(1)
    args += Doc.grouped(
        Doc.str("_capacityLeft =")
            + Doc.nested(4, Doc.break_(1) + self._capacityLeft.toDoc()),
    )
    args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
    Doc.grouped(Doc.str("HashMap") + Doc.char('(') + args)


impl[ToDoc[k], ToDoc[v]] ToDoc[Elem[k, v]]:
    toDoc(self: Elem[k, v]) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("key =") + Doc.nested(4, Doc.break_(1) + self.key.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("value =")
                + Doc.nested(4, Doc.break_(1) + self.value.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("next =") + Doc.nested(4, Doc.break_(1) + self.next.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("Elem") + Doc.char('(') + args)
