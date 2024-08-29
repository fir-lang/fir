prim type I32

prim type Bool

impl I32:
    prim fn __eq(self, other: I32): Bool
    prim fn __add(self, other: I32): I32

prim type Array[T]

type Option[T]:
    Some(T)
    None

impl[T] Array[T]:
    prim fn new(len: I32): Array[T]
    prim fn len(self): I32
    prim fn get(self, idx: I32): T
    prim fn set(self, idx: I32, elem: T): T

type ArrayIter[T]:
    array: Array[T]
    idx: I32

trait Iterator[T]:
    type Item

    fn next(self): Option[Item]

impl[T] Iterator[ArrayIter[T]]:
    type Item = T

    fn next(self): Option[T] =
        if self.idx == self.array.len():
            Option.None
        else:
            let idx = self.idx
            self.idx += 1
            Option.Some(self.array.get(idx))

# args: --typecheck --no-prelude
# expected stdout:
