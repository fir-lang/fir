prim type Str
prim type I32

type Bool:
    False
    True

toStr(self): Str
    Bool.False

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/TcFail2.fir:9:5: Unable to unify types Bool and Str
