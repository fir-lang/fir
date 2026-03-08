# Tests duplicate types in variants.

inner() [Option[U32], Bool, ..r]:
    ~Option.None

outer() [Bool, ..r]:
    match inner():
        ~Option.Some(_): ~Bool.True
        ~Option.None: ~Bool.False
        other: other

main():
    # `r = row[Option[U64]]` makes `inner`'s return type
    # `[Option[U32], B, Option[U64]`, which is not allowed (duplicate label).
    #
    # We can lift this restriction, there's no reason to not allow
    # `[Option[U32], Option[U64]]`. We may want to fix this in the self-hosted
    # compiler.
    match outer[row[Option[U64]], []]():
        ~Option.Some(_): print("Option")
        ~Option.None: print("Option")
        ~Bool.True: print("Bool")
        ~Bool.False: print("Bool")

# expected stderr: Type error: duplicate label in variant
