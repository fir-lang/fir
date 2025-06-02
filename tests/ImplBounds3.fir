prim type Array[t]

prim type U32

trait Ord[t]:
    cmp(self: t, other: t)

type Vec[t]:
    _data: Array[t]
    _len: U32

Vec.len(self: Vec[t]) U32:
    self._len

Vec.sort[Ord[t]](self: Vec[t]):
    _quicksort(self, 0, self.len())

_quicksort[Ord[t]](vec: Vec[t], low: U32, high: U32):
    ()

# args: --typecheck --no-backtrace --no-prelude
