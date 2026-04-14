trait Foo[t]:
    type Ext
    defaultExt() Foo[t].Ext

type Bar[t]:
    Baz(ext: Foo[t].Ext)

type MyFoo

impl Foo[MyFoo]:
    type Ext = ()
    defaultExt() Foo[MyFoo].Ext: ()

f[Foo[t], ToStr[Foo[t].Ext]](x: Bar[t]):
    match x:
        Bar.Baz(ext, ..): print(ext)

main():
    f[MyFoo, []](Bar.Baz(ext = ()))

# expected stdout:
# ()
