# Regression test: when resolving an associated type using the trait table, we
# should use one-way unification to the `impl` head instead of syntactic
# equality to unify type variables as we match `impl` arguments.

trait Seq[s, exn]:
    type Item
    first(self: s) Option[Seq[s, exn].Item] / exn

type MySeq(val: U32)

impl Seq[MySeq, exn]:
    type Item = U32
    first(self: MySeq) Option[Seq[MySeq, exn].Item] / exn:
        Option.Some(self.val)

type Wrapper[s, item, exn](inner: s)

impl[Seq[s, exn], Seq[s, exn].Item = item] Seq[Wrapper[s, item, exn], exn]:
    type Item = item
    first(self: Wrapper[s, item, exn]) Option[Seq[Wrapper[s, item, exn], exn].Item] / exn:
        self.inner.first()

main():
    let w = Wrapper(inner = MySeq(val = 42))
    let v: Option[U32] = w.first()
    print(v)

# expected stdout:
# Option.Some(42)
