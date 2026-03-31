main():
    print(Eq.__eq((msg = "hi", x = u32(123)), (x = u32(123), msg = "hi")))
    print(Eq.__eq((msg = "hi", x = u32(123)), (x = u32(124), msg = "hi")))


# expected stdout:
# Bool.True
# Bool.False
