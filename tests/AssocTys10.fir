# Test chained method calls requiring eager resolution of associated types.
#
# When we call `list.first()`, the return type involves `Container[t].Item`,
# which must be resolved eagerly so that `.unwrap()` can be type-checked on the
# concrete result type.

trait Container[t]:
    type Item

    firstUnchecked(self: t) Container[IntList].Item
    first(self: t) Option[Container[t].Item]

type IntList:
    Cons(I32, IntList)
    Nil

impl Container[IntList]:
    type Item = I32

    firstUnchecked(self: IntList) Container[IntList].Item:
        self.first().unwrap()

    first(self: IntList) Option[Container[IntList].Item]:
        match self:
            IntList.Cons(x, _): Option.Some(x)
            IntList.Nil: Option.None

main():
    let list = IntList.Cons(42, IntList.Nil)

    # Chained call: first() returns Option[Container[IntList].Item],
    # which must eagerly resolve Item = I32 so .unwrap() yields I32.
    let x: I32 = list.first().unwrap()
    print(x)
    print(list.firstUnchecked())

# expected stdout:
# 42
# 42
