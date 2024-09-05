prim type Str
prim type I32

prim fn printStr(s: Str): ()

trait ToStr[A]:
    fn toStr(self): Str

fn f[A](a: A) =
    printStr(a.toStr())

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr: tests/TraitFail1.fir:10:14: Type A does not have field or method toStr
