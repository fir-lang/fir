# Trait method with a predicate that references the trait's type parameter. The
# type checker needs to substitute the trait type param in predicates when
# checking that impl method signatures match the trait method signatures.

trait Container[a]:
    contains[Eq[a]](self: a, item: a) Bool

type Box(val: I32)

impl Eq[Box]:
    __eq(self: Box, other: Box) Bool:
        self.val == other.val

impl Container[Box]:
    contains[Eq[Box]](self: Box, item: Box) Bool:
        self == item

main():
    let b1 = Box(val = 1)
    let b2 = Box(val = 1)
    let b3 = Box(val = 2)
    printStr(b1.contains(b2).toStr())
    printStr(b1.contains(b3).toStr())

# expected stdout:
# Bool.True
# Bool.False
