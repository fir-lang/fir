main():
    let x = (a = u32(123), b = "hi", c = Bool.True)
    let y = (a = u32(456), ..x)

# The error message here is not ideal (we need "absent" predicates to properly
# reject this), but as long as we reject it it should be OK for now.

# expected exit status: 101
# expected stderr: BUG: Duplicate label in anonymous type (a: U32, ..row(a: U32, b: Str, c: Bool))
