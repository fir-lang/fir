impl[Foo[bar], Baz[t]] Iterator[VecIter[t], t, exn]:
    foo()

    bar()

    baz()

# expected stdout:
# impl[Foo[bar], Baz[t]] Iterator[VecIter[t], t, exn]:
#     foo()
# 
#     bar()
# 
#     baz()
