trait Container[c]:
    type Item
    first(self: c) Option[Container[c].Item]

impl Container[MyContainer]:
    type Item = U32
    first(self: MyContainer) Option[Container[MyContainer].Item]:
        Option.Some(self.val)

type MyContainer(val: U32)

# A generic function with an associated type equality constraint. This exercises
# resolving `Container[c].Item` to `item` via the equality constraint (not via a
# concrete impl lookup).
consumeOne[Container[c], Container[c].Item = item](c: c) item:
    c.first().unwrap()

main():
    let c = MyContainer(val = 42)
    print(consumeOne(c))

# expected stdout:
# 42
