# Test two impls of the same trait with different associated types, and a
# generic function that works with both.

trait Container[t]:
    type Item

    first(self: t) Option[Container[t].Item]

type IntList:
    ICons(I32, IntList)
    INil

type StrList:
    SCons(Str, StrList)
    SNil

impl Container[IntList]:
    type Item = I32

    first(self: IntList) Option[Container[IntList].Item]:
        match self:
            IntList.ICons(x, _): Option.Some(x)
            IntList.INil: Option.None

impl Container[StrList]:
    type Item = Str

    first(self: StrList) Option[Container[StrList].Item]:
        match self:
            StrList.SCons(x, _): Option.Some(x)
            StrList.SNil: Option.None

printFirst[Container[t], ToStr[Container[t].Item]](c: t):
    match c.first():
        Option.Some(x): print(x)
        Option.None: print("empty")

main():
    printFirst(IntList.ICons(42, IntList.INil))
    printFirst(StrList.SCons("hello", StrList.SNil))
    printFirst(IntList.INil)

# expected stdout:
# 42
# hello
# empty
