trait Step[T: Ord]:
    fn next(self): T

impl Step for U32:
    fn next(self): U32 = self + 1

type T:
    i: I32

impl Step for T:
    fn next(self): T = T(i = self.i + 1)

# args: --typecheck --no-backtrace
# expected stderr: tests/TraitFail4.fir:10:1: Type T does not implement Ord
