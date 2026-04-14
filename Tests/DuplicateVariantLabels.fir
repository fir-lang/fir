# Tests duplicate types in variants.

type A

type B

inner() [A, B, ..r]:
    ~A

outer() [B, ..r]:
    match inner():
        ~A: ~B
        other: other

main():
    # `r = row[A]` makes `inner`'s return type `[A, B, A]`.
    match outer[row[A], []]():
        ~A: print("A")
        ~B: print("B")

# expected stdout: B
