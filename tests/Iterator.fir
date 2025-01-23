type Bool:
    True
    False

prim type I32

trait Eq[t]:
    __eq(self, other: t): Bool

trait Add[t]:
    __add(self, other: t): t

impl Eq for I32:
    prim __eq(self, other: I32): Bool

impl Add for I32:
    prim __add(self, other: I32): I32

type Option[t]:
    None
    Some(t)

trait Iterator[t]:
    type Item

    next(self): Option[Item]

prim type Array[t]

prim Array[t].len(self): I32
prim Array[t].get(self, idx: I32): t

type ArrayIter[t]:
    array: Array[t]
    idx: I32

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
