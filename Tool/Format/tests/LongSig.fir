topFunSig(state: ParserState[Token]) (parentTy: Option[Id], name: Id, sig: FunSig) / U32:
    1

# Right paren at column 81.
runParser(input: Str, parseFn: Fn(ParserState[Token]) tree / U32, runScan: Bool,) tree / TestError:
    ()

HashSet.iter(self: HashSet[k]) Map[HashMapIter[k, ()], HashMapEntry[k, ()], k, exn]:
    self._map.iter().map(\(kv) k: kv.key)

HashSet.difference[Hash[k], Eq[k]](self: HashSet[k], other: HashSet[k]) Filter[Map[HashMapIter[k, ()], HashMapEntry[k, ()], k, exn], k, exn]:
    self.iter().filter(\(k: k): not other.contains(k))

# expected stdout:
# topFunSig(
#     state: ParserState[Token],
# ) (parentTy: Option[Id], name: Id, sig: FunSig) / U32:
#     1
# 
# 
# # Right paren at column 81.
# runParser(
#     input: Str,
#     parseFn: Fn(ParserState[Token]) tree / U32,
#     runScan: Bool,
# ) tree / TestError:
#     ()
# 
# 
# HashSet.iter(
#     self: HashSet[k],
# ) Map[HashMapIter[k, ()], HashMapEntry[k, ()], k, exn]:
#     self._map.iter().map(\(kv) k: kv.key)
# 
# 
# HashSet.difference[Hash[k], Eq[k]](
#     self: HashSet[k],
#     other: HashSet[k],
# ) Filter[Map[HashMapIter[k, ()], HashMapEntry[k, ()], k, exn], k, exn]:
#     self.iter().filter(\(k: k): not other.contains(k))
