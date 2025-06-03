trait Test[t1, t2]:
    test(self: t1) t2

impl Test[U32, U32]:
    test(self: U32) U32:
        self

main():
    let x: U32 = 123u32.test()

prim type Str
prim type U32
prim printStr(s: Str)

# args: --typecheck --no-prelude
