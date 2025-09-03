impl[Foo[bar], Baz] Iterator[VecIter[t], t, exn]:
    foo()

    bar()

    baz()

# expected stdout:
# impl[Foo[bar], Baz] Iterator[VecIter[t], t, exn]:
#     foo()
# 
#     bar()
# 
#     baz()
