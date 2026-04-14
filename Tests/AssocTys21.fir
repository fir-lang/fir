trait Seq[s]:
    type Item
    transform(self: s, f: Fn(Seq[s].Item) b / exn) b / exn

type Pair(fst: U32, snd: U32)

type PairSeq(fst: U32, snd: U32)

impl Seq[PairSeq]:
    type Item = Pair
    transform(self: PairSeq, f: Fn(Seq[PairSeq].Item) b / exn) b / exn:
        f(Pair(fst = self.fst, snd = self.snd))

main():
    let s = PairSeq(fst = 1, snd = 2)
    # After unification resolves the self type, the method return type contains
    # `AssocTySelect` that needs `deep_normalize` to resolve.
    # The lambda param `p` has type `Seq[PairSeq].Item` which should resolve to
    # `Pair`.
    let result = s.transform(\(p): p.fst)
    print(result)

# expected stdout:
# 1
