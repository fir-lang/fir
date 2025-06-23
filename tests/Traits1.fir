trait Test[t]:
    test(self: t)

impl Test[U32]:
    test(self: U32):
        printStr("U32.test")

main():
    u32(123).test()

u32(i: U32) U32 = i
prim type Str
prim type U32
prim printStr(s: Str)

# args: --typecheck --no-prelude
