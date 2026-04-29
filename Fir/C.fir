#[include("stddef.h", "stdio.h")]
import []


extern type Int = "int"


extern type SizeT = "size_t"


extern type File = "FILE"


extern type Ptr[t] = "`t`*"


extern type DivT = "div_t"(
    quot: I32 = "quot",
    rem: I32 = "rem",
)


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


div(num: I32, den: I32) DivT:
    inline("div(`num`, `den`)")


Ptr.isNull(self: Ptr[t]) Int:
    inline("`self` == NULL")


Ptr.deref(self: Ptr[t]) t:
    inline("*`self`")


# We'll probably allow converting arrays to C pointers. This is needed for
# passing buffers to C.
prim Array.ptr(self: Array[t]) Ptr[t]
