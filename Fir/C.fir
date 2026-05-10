#[include("stddef.h", "stdio.h")]
import []


extern type Int = "int"


## The libc `size_t` type.
extern type SizeT = "size_t"


## The libc `ssize_t` type.
extern type SSizeT = "ssize_t"


## This is the C pointer type, e.g. `Ptr[Foo]` becomes `Foo*` in C.
##
## This type is specially handled by the compiler to allow field access and
## updates behind pointers.
prim type Ptr[t]


## The C `void` type.
extern type Void = "void"


## An inline C directive.
##
## The argument should be a string literal and it can have interpolations. The
## type checker specially handles calls to this function to type the string
## literal as `Template` instead of `Str`. The argument cannot be anything other
## than a string literal.
prim inline(template: Template) a


## Type for the string literals used as the argument to `inline`.
##
## These values are not first-class, the type checker special cases `inline`
## calls (defined below) to give this type to string literals in `inline`.
prim type Template


Ptr.isNull(self: Ptr[t]) Bool / exn:
    inline[U32, exn]("(uint32_t)(`self` == NULL)") != 0


Ptr.deref(self: Ptr[t]) t:
    inline("*`self`")


# We'll probably allow converting arrays to C pointers. This is needed for
# passing buffers to C.
prim Array.ptr(self: Array[t]) Ptr[t]
