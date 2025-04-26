type T1:
    a: U32

type T2:
    a: U32

T1.foo(self)
    print("T1.foo(a = `self.a`)")

T2.foo(self)
    print("T2.foo(a = `self.a`)")

main
    let t1 = T1(a = 1u32)
    let t2 = T2(a = 2u32)
    t1.foo()
    t2.foo()

# expected stdout:
# T1.foo(a = 1)
# T2.foo(a = 2)
