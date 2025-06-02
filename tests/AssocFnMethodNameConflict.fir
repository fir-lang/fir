type T1:
    a: U32

trait Foo[t]:
    foo(self: t)

T1.foo(self):
    print("(associated) T1.foo(a = `self.a`)")

impl Foo[T1]:
    foo(self: T1):
        print("(trait) T1.foo(a = `self.a`)")

main():
    let t1 = T1(a = 1u32)
    t1.foo()

    # Test standard library `Option.map` colliding with `Iterator.map`
    print(Option.Some(123u32).map(fn(i: U32): Str { i.toStr() }))

# expected stdout:
# (associated) T1.foo(a = 1)
# Option.Some(123)
