prim type I32

prim type Bool

impl I32:
    prim __eq(self, other: I32): Bool
    prim __add(self, other: I32): I32

prim type Array[t]

type Option[t]:
    Some(t)
    None

prim Array[t].new(len: I32): Array[t]
prim Array[t].len(self): I32
prim Array[t].get(self, idx: I32): t
prim Array[t].set(self, idx: I32, elem: t)

type ArrayIter[t]:
    array: Array[t]
    idx: I32

trait Iterator[t]:
    type Item

    next(self): Option[Item]

impl[t] Iterator for ArrayIter[t]:
    type Item = t

    next(self): Option[t]
        if self.idx == self.array.len():
            Option.None
        else:
            let idx = self.idx
            self.idx += 1
            Option.Some(self.array.get(idx))

# args: --typecheck --no-prelude
# expected stdout:
