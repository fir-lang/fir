prim type Array[T]

prim type U32

trait Ord[T]:
    fn cmp(self, other: T)

type Vec[T]:
    _data: Array[T]
    _len: U32

impl[T] Vec[T]:
    fn len(self): U32 =
        self._len

impl[T: Ord] Vec[T]:
    fn sort(self) =
        _quicksort(self, 0, self.len())

fn _quicksort[T: Ord](vec: Vec[T], low: U32, high: U32) =
    ()

# args: --typecheck --no-backtrace --no-prelude
