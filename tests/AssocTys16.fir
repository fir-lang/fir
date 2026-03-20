trait Container[c]:
    type Item
    first(self: c) Option[Container[c].Item]

type Box[t](val: t)

impl Container[Box[t]]:
    type Item = t
    first(self: Box[t]) Option[Container[Box[t]].Item]: Option.Some(self.val)

consume[Container[c], Container[c].Item = item](c: c) Vec[item]:
    let v: Vec[item] = Vec.empty()
    v.push(c.first().unwrap())
    v

# The `Box` is created with `Option.None`, so its type is `Box[Option[_t]]`
# where `_t` is unresolved. The return type annotation resolves `item` to
# `Option[U32]`. The pred `Container[Box[Option[_t]]].Item = Option[U32]` must
# resolve, which requires unifying `_t` with `U32`, but one-way unification
# can't do this because the `UVar` is on the right.
main():
    let b = Box(val = Option.None)
    let result: Vec[Option[U32]] = consume(b)
    print(result.get(0))

# expected stdout:
# Option.None
