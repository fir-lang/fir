trait Foo[t]:
    foo(self: t) Str

impl Foo[(..r)]:
    foo(self: (..r)) Str:
        "record"

main():
    let x: [] = panic("unreachable")
    print(Foo.foo(x))

# expected exit status: 101
# expected stderr:
# Unable to resolve predicates:
# Tests/RecordVariantOneWayUnificationFail.fir:10:11: Foo[[]]
