trait Container[c]:
    type Elem

    get(self: c, idx: U32) Elem

type MyVec(items: Array[U32])

impl Container[MyVec]:
    type Elem = U32

    get(self: MyVec, idx: U32) U32:
        self.items.get(idx)

main():
    let a: Array[U32] = Array.new(3)
    a.set(0, 1)
    a.set(1, 2)
    a.set(2, 3)
    let v = MyVec(items = a)
    printStr(v.get(0).toStr())
    printStr(v.get(1).toStr())
    printStr(v.get(2).toStr())

# expected stdout:
# 1
# 2
# 3
