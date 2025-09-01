f():
    # Named types
    let x: T[t1, t2] = a
    let x: T[t1, t2,] = a

    # Record types
    let x: (x: U32, y: U32) = a
    let x: (x: U32, y: U32,) = a

    # Variant types
    let x: [A, B] = a
    let x: [A, B,] = a

    # Fn types, args
    let x: Fn(U32, U32) = a
    let x: Fn(U32, U32,) = a

    # Con fields
    match x:
        X(a, b): ()
        X(a, b,): ()
        X(a, b, ..): ()

    # Record fields
    match x:
        (a, b): ()
        (a, b,): ()
        (a, b, ..): ()

    # Fun args
    f(x, y)
    f(x, y,)

    # Con args
    C(x, y)
    C(x, y,)

    # Record args
    (x, y)
    (x, y,)

    # Sequences
    Vec.[1, 2]
    Vec.[1, 2,]


# Contexts
f[T1, T2](): ()

f[T1, T2,](): ()

# Param lists
f(x: U32, y: U32): ()
f(x: U32, y: U32,): ()

# Impl contexts
impl[T1, T2] T[A]:
    f(): ()

impl[T1, T2,] T[A]:
    f(): ()

# Impl args
impl T[A, B]:
    f(): ()

impl T[A, B,]:
    f(): ()

# Trait args

trait Foo[a, b]:
    f(): ()

trait Foo[a, b,]:
    f(): ()

# expected stdout:
# f():
#     # Named types
#     let x: T[t1, t2] = a
#     let x: T[t1, t2,] = a
# 
#     # Record types
#     let x: (x: U32, y: U32) = a
#     let x: (x: U32, y: U32,) = a
# 
#     # Variant types
#     let x: [A, B] = a
#     let x: [A, B,] = a
# 
#     # Fn types, args
#     let x: Fn(U32, U32) = a
#     let x: Fn(U32, U32,) = a
# 
#     # Con fields
#     match x:
#         X(a, b): ()
#         X(a, b,): ()
#         X(a, b, ..): ()
# 
#     # Record fields
#     match x:
#         (a, b): ()
#         (a, b,): ()
#         (a, b, ..): ()
# 
#     # Fun args
#     f(x, y)
#     f(x, y,)
# 
#     # Con args
#     C(x, y)
#     C(x, y,)
# 
#     # Record args
#     (x,
#         y,)
#     (x, y,)
# 
#     # Sequences
#     Vec.[1,
#         2,
#     ]
#     Vec.[1, 2,]
# 
# 
# # Contexts
# f[T1, T2]():
#     ()
# 
# 
# f[T1, T2,]():
#     ()
# 
# 
# # Param lists
# f(x: U32, y: U32):
#     ()
# 
# 
# f(x: U32, y: U32,):
#     ()
# 
# 
# # Impl contexts
# impl[T1, T2] T[A]:
#     f():
#         ()
# 
# 
# impl[T1, T2,] T[A]:
#     f():
#         ()
# 
# 
# # Impl args
# impl T[A, B]:
#     f():
#         ()
# 
# 
# impl T[A, B,]:
#     f():
#         ()
# 
# 
# # Trait args
# 
# trait Foo[a, b]:
#     f():
#         ()
# 
# 
# trait Foo[a, b,]:
#     f():
#         ()
