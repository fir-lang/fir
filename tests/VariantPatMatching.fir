f1() [Str, Char, Bool]:
    ~"hi"

f2() [Str, Char, Bool]:
    ~'a'


f3() [Str, Char, Bool]:
    ~Bool.True

main():
    match f1():
        ~'a': print("1")
        ~Bool.True: print("2")
        ~"hi": print("3")

    match f2():
        ~Bool.True: print("1")
        ~"hi": print("2")
        ~'a': print("3")

    match f3():
        ~"hi": print("1")
        ~'a': print("2")
        ~Bool.True: print("3")

# expected stdout:
# 3
# 3
# 3

# expected stderr:
# tests/VariantPatMatching.fir:12:5: Unexhaustive pattern match
# tests/VariantPatMatching.fir:17:5: Unexhaustive pattern match
# tests/VariantPatMatching.fir:22:5: Unexhaustive pattern match
