trait Seq[s, exn]:
    type Item
    first(self: s) Option[Seq[s, exn].Item] / exn

type MySeq(val: U32)

impl Seq[MySeq, exn]:
    type Item = U32
    first(self: MySeq) Option[Seq[MySeq, exn].Item] / exn:
        Option.Some(self.val)

type Wrapper[s, exn](inner: s)

impl[Seq[s, exn]] Seq[Wrapper[s, exn], exn]:
    type Item = Seq[s, exn].Item
    first(self: Wrapper[s, exn]) Option[Seq[Wrapper[s, exn], exn].Item] / exn:
        self.inner.first()

main():
    # This makes the first trait arg concrete, while the trait-level `exn`
    # `UVar` stays unlinked.
    let w: Wrapper[MySeq, []] = Wrapper(inner = MySeq(val = 42))

    # When finding the impl, generate `Seq[MySeq, []]`, and then the return type
    # becomes `Option[Seq[Wrapper[MySeq, []], []].Item]`, which is reduced to
    # `Option[Seq[MySeq, []].Item]`, where the associated type's trait part
    # should should match the first `impl` and get reduced to `U32`.
    let v: Option[U32] = w.first()

    print(v)

# expected stdout:
# Option.Some(42)
