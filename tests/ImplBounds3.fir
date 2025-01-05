prim type Array[t]

prim type U32

trait Ord[t]:
    fn cmp(self, other: t)

type Vec[t]:
    _data: Array[t]
    _len: U32

impl[t] Vec[t]:
    fn len(self): U32 =
        self._len

impl[t: Ord] Vec[t]:
    fn sort(self) =
        _quicksort(self, 0, self.len())

fn _quicksort[t: Ord](vec: Vec[t], low: U32, high: U32) =
    ()

# args: --typecheck --no-backtrace --no-prelude
