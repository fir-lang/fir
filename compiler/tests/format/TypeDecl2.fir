type Foo(U32, U32)

type Foo(
    x: U32,
    y: U32,
)

type Foo(
    x: U32,

    y: U32,
)

type Foo(
    # hi
    x: U32,
    # hi
    y: U32,
)

# expected stdout:
# type Foo(U32, U32)
# 
# 
# type Foo(
#     x: U32,
#     y: U32,
# )
# 
# 
# type Foo(
#     x: U32,
#     
#     y: U32,
# )
# 
# 
# type Foo(
#     # hi
#     x: U32,
#     
#     # hi
#     y: U32,
# )
