# Test omitting empty parameter lists.
#
# This is not too useful for now, but it may become useful if we make `self`
# parameters implicit in methods.

fn f1
    printStr("f1")

fn f2 = printStr("f2")

fn f3[]
    printStr("f3")

fn f4[] = printStr("f4")

fn main
    f1()
    f2()
    f3()
    f4()

# expected stdout:
# f1
# f2
# f3
# f4
