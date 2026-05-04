extern type Foo = "struct foo"


extern type Foo = "struct foo"()


extern type Foo = "struct foo"(
    x: U32 = "a",
    y: U32 = "b",
)


extern type Foo = "struct foo"(
    x: U32 = "aaaaaaaaa",
    y: U32 = "bbbbbbbbb",
    z: U32 = "ccccccccc",
)

# expected stdout:
# extern type Foo = "struct foo"
# 
# 
# extern type Foo = "struct foo"(
# 
# )
# 
# 
# extern type Foo = "struct foo"(
#     x: U32 = "a",
#     y: U32 = "b",
# )
# 
# 
# extern type Foo = "struct foo"(
#     x: U32 = "aaaaaaaaa",
#     y: U32 = "bbbbbbbbb",
#     z: U32 = "ccccccccc",
# )
