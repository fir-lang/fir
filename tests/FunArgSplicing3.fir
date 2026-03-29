type Foo[extras: Row[Rec]](x: U32, ..extras)

main():
    let rest = (y = u32(2), z = "hello")
    let f = Foo(x = u32(1), ..rest)
    print(f.x)
    print(f.y)
    print(f.z)

# expected stdout:
# 1
# 2
# hello
