#[NoImplicitPrelude]
import []

type Type1

type Type2[t]

trait Ord[t]:
    cmp(self: t, other: t)

type Vec[t](
    _data: Type2[t],
    _len: Type1,
)

Vec.len(self: Vec[t]) Type1:
    self._len

Vec.sort[Ord[t]](self: Vec[t]):
    _quicksort(self, Type1, self.len())

_quicksort[Ord[t]](vec: Vec[t], low: Type1, high: Type1):
    ()

# args: --typecheck
