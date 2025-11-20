type HashSet[k](
    _map: HashMap[k, ()],
)


HashSet.empty() HashSet[k]:
    HashSet.withCapacity(0)


HashSet.withCapacity(cap: U32) HashSet[k]:
    HashSet(_map = HashMap.withCapacity(cap))


HashSet.len(self: HashSet[k]) U32:
    self._map.len()


HashSet.isEmpty(self: HashSet[k]) Bool:
    self._map.isEmpty()


HashSet.fromIter[Iterator[iter, k, exn], Eq[k], Hash[k]](iter: iter) HashSet[k] / exn:
    HashSet(_map = HashMap.fromIter(iter.map(|k|: (key = k, value = ()))))


HashSet.iter(self: HashSet[k]) Map[HashMapIter[k, ()], HashMapEntry[k, ()], k, exn]:
    self._map.iter().map(|kv| k: kv.key)


## Returns whether the value is newly inserted.
HashSet.insert[Hash[k], Eq[k]](self: HashSet[k], key: k) Bool:
    self._map.insert(key, ()) is Option.None


HashSet.contains[Hash[k], Eq[k]](self: HashSet[k], key: k) Bool:
    self._map.get(key) is Option.Some(_)


HashSet.difference[Hash[k], Eq[k]](self: HashSet[k], other: HashSet[k]) Filter[Map[HashMapIter[k, ()], HashMapEntry[k, ()], k, exn], k, exn]:
    self.iter().filter(|k: k|: not other.contains(k))


HashSet.intersection[Hash[k], Eq[k]](self: HashSet[k], other: HashSet[k]) Filter[Map[HashMapIter[k, ()], HashMapEntry[k, ()], k, exn], k, exn]:
    self.iter().filter(|k: k|: other.contains(k))


impl[Hash[k], Eq[k]] Eq[HashSet[k]]:
    __eq(self: HashSet[k], other: HashSet[k]) Bool:
        if self.len() != other.len():
            return Bool.False

        for k: k in self.iter():
            if not other.contains(k):
                return Bool.False

        Bool.True


impl[ToStr[k]] ToStr[HashSet[k]]:
    toStr(self: HashSet[k]) Str:
        let buf = StrBuf.withCapacity(100)
        buf.push('{')
        let printed = 0
        for elem: k in self.iter():
            if printed != 0:
                buf.pushStr(", ")
            buf.pushStr(elem.toStr())
            printed += 1
        buf.push('}')
        buf.toStr()


impl[ToDoc[k]] ToDoc[HashSet[k]]:
    toDoc(self: HashSet[k]) Doc:
        let elems = Doc.empty()
        let printed: U32 = 0
        for elem: k in self.iter():
            if printed != 0:
                elems += Doc.char(',') + Doc.break_(1)
            elems += elem.toDoc()
            printed += 1

        if printed != 0:
            elems += Doc.whenNotFlat(Doc.char(','))

        Doc.grouped(
            Doc.str("HashSet.[")
                + Doc.nested(4, Doc.break_(0) + elems)
                + Doc.break_(0)
                + Doc.char(']'),
        )
