type T:
    i: I32

impl T:
    fn print(self) =
        printStr("T(i = `self.i`)")

type MyBool:
    False
    True

impl MyBool:
    fn print(self) =
        match self:
            MyBool.False: printStr("False")
            MyBool.True: printStr("True")

fn main(input: Str) =
    let a = T(i = 123).print
    let b = MyBool.True.print
    let c = MyBool.False.print
    a()
    b()
    c()

# expected stdout:
# T(i = 123)
# True
# False
