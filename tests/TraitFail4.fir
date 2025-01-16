trait Step2[t: Ord]:
    next(self): t

impl Step2 for U32:
    next(self): U32 = self + 1

type T:
    i: I32

impl Step2 for T:
    next(self): T = T(i = self.i + 1)

# args: --typecheck --no-backtrace
# expected stderr: tests/TraitFail4.fir:10:1: Type T does not implement Ord
