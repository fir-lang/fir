trait Seq[s]:
    type Item
    first(self: s) Option[Seq[s].Item]

type MySeq(val: U32)

impl Seq[MySeq]:
    type Item = U32
    first(self: MySeq) Option[Seq[MySeq].Item]:
        Option.Some(self.val)

getFirst[Seq[s], Seq[s].Item = item](s: s) Option[item]:
    s.first()

wrapFirst[Seq[s], Seq[s].Item = item](s: s) Vec[Option[item]]:
    let v: Vec[Option[item]] = Vec.empty()
    v.push(getFirst(s))
    v

main():
    let s = MySeq(val = 42)
    print(wrapFirst(s))

# expected stdout:
# [Option.Some(42)]
