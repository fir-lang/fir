# It's OK when the same definition comes via different import paths.

#[NoImplicitPrelude]
import [
    Tests/Modules/Conflicts3/Lib3,
]


main():
    let _ = Foo.A
    ()


# args: --typecheck
