type T:
    i: I32

T.print(self):
    printStr("T(i = `self.i`)")

type MyBool:
    False
    True

MyBool.print(self):
    match self:
        MyBool.False: printStr("False")
        MyBool.True: printStr("True")

main():
    let a = T(i = 123).print
    let b = MyBool.True.print
    let c = MyBool.False.print
    let d: Fn(U32) Vec[U32] / [] = Vec.withCapacity
    let e: Fn(Vec[U32]) U32 / [] = Vec.len
    let f: Fn(Str) Option[Str] / [] = Option.Some
    a()
    b()
    c()

    let vec = d(3u32)
    printStr(e(vec).toStr())

    match f("Hi"):
        Option.None: panic("")
        Option.Some(msg): printStr(msg)

# expected stdout:
# T(i = 123)
# True
# False
# 0
# Hi
