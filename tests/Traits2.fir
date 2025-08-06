trait Test[t1, t2]:
    test(self: t1) t2

impl Test[U32, U32]:
    test(self: U32) U32:
        self

main():
    let x: U32 = u32(123).test()

u32(i: U32) U32: i
prim type Str
prim type U32
prim printStr(s: Str)

# args: --typecheck --no-prelude
