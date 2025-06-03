trait Test[t]:
    test(self: t)

impl Test[U32]:
    test(self: U32):
        printStr("U32.test")

main():
    123u32.test()

prim type Str
prim type U32
prim printStr(s: Str)

# args: --typecheck --no-prelude
