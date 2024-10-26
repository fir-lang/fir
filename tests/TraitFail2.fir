prim type Str
prim type I32

prim fn printStr(s: Str): ()

trait ToStr[A]:
    fn toStr(self): Str

fn f[A: ToStr](a: A) =
    printStr(a.toStr())

fn g() = f(123u32)

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/TraitFail2.fir:12:10: Type U32 does not implement trait ToStr
