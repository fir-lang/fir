expectU32(x: U32):
    ()

foo() Option[U32]:
    Option.None

main():
    print("`foo() is Option.None`")

# expected stdout: Bool.True
