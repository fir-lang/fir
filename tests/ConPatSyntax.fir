type C(
    x: U32,
    y: U32,
)

type S:
    S1(x: U32, y: U32)

f1() C:
    C(x = 123, y = 456)

f2() S:
    S.S1(x = 123, y = 456)

f3() (x: U32, y: U32):
    (x = 123, y = 123)

main():
    match f1():
        C(..): print("..")

    match f1():
        C(x, ..): print("x=`x`")

    match f1():
        C(x, y, ..): print("x=`x`, y=`y`")

    match f1():
        C(x, y): print("x=`x`, y=`y`")

    match f2():
        S.S1(..): print("..")

    match f2():
        S.S1(x, ..): print("x=`x`")

    match f2():
        S.S1(x, y, ..): print("x=`x`, y=`y`")

    match f2():
        S.S1(x, y): print("x=`x`, y=`y`")

    match f3():
        (..): print("..")

    match f3():
        (x, ..): print("x=`x`")

    match f3():
        (x, y, ..): print("x=`x`, y=`y`")

    match f3():
        (x, y): print("x=`x`, y=`y`")

# expected stdout:
# ..
# x=123
# x=123, y=456
# x=123, y=456
# ..
# x=123
# x=123, y=456
# x=123, y=456
# ..
# x=123
# x=123, y=123
# x=123, y=123
