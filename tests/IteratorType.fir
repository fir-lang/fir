prim type I32

prim type Bool

impl I32:
    prim fn __eq(self, other: I32): Bool
    prim fn __add(self, other: I32): I32

prim type Array[t]

type Option[t]:
    Some(t)
    None

impl[t] Array[t]:
    prim fn new(len: I32): Array[t]
    prim fn len(self): I32
    prim fn get(self, idx: I32): t
    prim fn set(self, idx: I32, elem: t): t

type ArrayIter[t]:
    array: Array[t]
    idx: I32

trait Iterator[t]:
    type Item

    fn next(self): Option[Item]

impl[t] Iterator[ArrayIter[t]]:
    type Item = t

    fn next(self): Option[t]
        if self.idx == self.array.len():
            Option.None
        else:
            let idx = self.idx
            self.idx += 1
            Option.Some(self.array.get(idx))

# args: --typecheck --no-prelude
# expected stdout:
