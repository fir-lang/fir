type Foo(
    field1: Str,
    field2: Str,
    field3: Str,
    ..exts
)

type Foo(
    ## Line 1
    field1: Str,
    ## Line 2
    field2: Str,
    ## Line 3
    field3: Str,
    ## Line 4
    ..exts
)

type Foo(
    field1: Str,

    field2: Str,

    field3: Str,

    ..exts
)

type Foo(
    ## Line 1
    field1: Str,

    ## Line 2
    field2: Str,

    ## Line 3
    field3: Str,

    ## Line 4
    ..exts
)

type Foo(
    field1: Str,


    field2: Str,


    field3: Str,

    
    ..exts
)


type Foo(
    ## Line 1
    field1: Str,


    ## Line 2
    field2: Str,


    ## Line 3
    field3: Str,

    
    ## Line 4
    ..exts
)

# expected stdout:
# type Foo(
#     field1: Str,
#     field2: Str,
#     field3: Str,
#     ..exts
# )
# 
# 
# type Foo(
#     ## Line 1
#     field1: Str,
# 
#     ## Line 2
#     field2: Str,
# 
#     ## Line 3
#     field3: Str,
# 
#     ## Line 4
#     ..exts
# )
# 
# 
# type Foo(
#     field1: Str,
# 
#     field2: Str,
# 
#     field3: Str,
# 
#     ..exts
# )
# 
# 
# type Foo(
#     ## Line 1
#     field1: Str,
# 
#     ## Line 2
#     field2: Str,
# 
#     ## Line 3
#     field3: Str,
# 
#     ## Line 4
#     ..exts
# )
# 
# 
# type Foo(
#     field1: Str,
# 
#     field2: Str,
# 
#     field3: Str,
# 
#     ..exts
# )
# 
# 
# type Foo(
#     ## Line 1
#     field1: Str,
# 
#     ## Line 2
#     field2: Str,
# 
#     ## Line 3
#     field3: Str,
# 
#     ## Line 4
#     ..exts
# )
