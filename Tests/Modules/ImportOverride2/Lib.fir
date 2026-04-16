type Foo(
    a: Str,
    b: Str,
)


Foo.test(self):
    print("Lib/Foo(a = `self.a`, b = `self.b`)")
