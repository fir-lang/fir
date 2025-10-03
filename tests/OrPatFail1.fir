type Test:
    T1(Str)
    T2(U32)

main():
    match f():
        Test.T1(a) | Test.T2(a): print(a)

f() Test:
    Test.T1("hi")

# expected exit status: 101
# expected stderr: tests/OrPatFail1.fir:7:9: Unable to unify types Str and U32
