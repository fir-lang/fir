main():
    let x = (
        a = do: # test
            print("hi") # test
            u32(123), # test
        b = u32(456) # test
    )
    print(x.a)
    print(x.b)

# expected stdout:
# hi
# 123
# 456
