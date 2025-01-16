# Test omitting empty parameter lists.
#
# This is not too useful for now, but it may become useful if we make `self`
# parameters implicit in methods.

f1
    printStr("f1")

f2 = printStr("f2")

f3[]
    printStr("f3")

f4[] = printStr("f4")

main
    f1()
    f2()
    f3()
    f4()

# expected stdout:
# f1
# f2
# f3
# f4
