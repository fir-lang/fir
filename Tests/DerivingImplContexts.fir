# Bug: the generated `impl` context here should have `ToDoc[Bar[t]]` instead of
# `Bar[t]`.
#[derive(ToDoc)]
type Foo[t](
    x: Bar[t],
)


type Bar[t](
    x: t
)


# Note: impl doesn't require `ToDoc[t]`.
impl ToDoc[Bar[t]]:
    toDoc(self: Bar[t]) Doc:
        Doc.str("Bar")


# A non-`ToDoc` type.
type MyStr(
    str: Str
)


main():
    print(Foo(x = Bar(x = MyStr(str = "hi"))).toDoc().render(80))

# expected stdout: Foo(x = Bar)
