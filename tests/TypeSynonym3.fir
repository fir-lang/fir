trait Container[c]:
    type Elem

    get(self: c, idx: U32) Elem

type MyVec(items: Array[U32])

impl Container[MyVec]:
    type Elem = U32

    get(self: MyVec, idx: U32) Elem:
        self.items.get(idx)

main():
    let a: Array[U32] = Array.new(3)
    a.set(0, 10)
    a.set(1, 20)
    a.set(2, 30)
    let v = MyVec(items = a)
    printStr(v.get(1).toStr())

# expected stdout:
# 20
