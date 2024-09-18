type Bool:
    True
    False

prim type I32

trait Eq[T]:
    fn __eq(self, other: T): Bool

trait Add[T]:
    fn __add(self, other: T): T

impl Eq for I32:
    prim fn __eq(self, other: I32): Bool

impl Add for I32:
    prim fn __add(self, other: I32): I32

type Option[T]:
    None
    Some(T)

trait Iterator[T]:
    type Item

    fn next(self): Option[Item]

prim type Array[T]

impl[T] Array[T]:
    prim fn len(self): I32
    prim fn get(self, idx: I32): T

type ArrayIter[T]:
    array: Array[T]
    idx: I32

impl[T] Iterator for ArrayIter[T]:
    type Item = T

    fn next(self): Option[T] =
        if self.idx == self.array.len():
            Option.None
        else:
            let idx = self.idx
            self.idx += 1
            Option.Some(self.array.get(idx))

# args: --typecheck --no-prelude
