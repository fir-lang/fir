import [Fir/C as C]


# With a field list (empty here) we allow constructing the type.
extern type Empty = "struct { int _unused; }"()


mkEmpty() Empty:
    Empty()


main():
    mkEmpty()
    printStr("ok")


# expected stdout:
# ok
