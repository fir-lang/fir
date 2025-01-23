prim type Array[t]

prim type U32

trait Ord[t]:
    cmp(self, other: t)

type Vec[t]:
    _data: Array[t]
    _len: U32

Vec[t].len(self): U32
    self._len

Vec[t: Ord].sort(self)
    _quicksort(self, 0, self.len())

_quicksort[t: Ord](vec: Vec[t], low: U32, high: U32)
    ()

# args: --typecheck --no-backtrace --no-prelude
