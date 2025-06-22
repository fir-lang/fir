main():
    do:
        print("Hi")

    let x = (a = u32(1), b = do:
        print("In record expr")
        'a', c = "Bye")

    print(x.a)
    print(x.b)
    print(x.c)

# expected stdout:
# Hi
# In record expr
# 1
# 'a'
# Bye
