type Bool:
    True
    False

prim type I32

trait Eq[t]:
    fn __eq(self, other: t): Bool

trait Add[t]:
    fn __add(self, other: t): t

impl Eq for I32:
    prim fn __eq(self, other: I32): Bool

impl Add for I32:
    prim fn __add(self, other: I32): I32

type Option[t]:
    None
    Some(t)

trait Iterator[t]:
    type Item

    fn next(self): Option[Item]

prim type Array[t]

impl[t] Array[t]:
    prim fn len(self): I32
    prim fn get(self, idx: I32): t

type ArrayIter[t]:
    array: Array[t]
    idx: I32

impl[t] Iterator for ArrayIter[t]:
    type Item = t

    fn next(self): Option[t]
        if self.idx == self.array.len():
            Option.None
        else:
            let idx = self.idx
            self.idx += 1
            Option.Some(self.array.get(idx))

# args: --typecheck --no-prelude
