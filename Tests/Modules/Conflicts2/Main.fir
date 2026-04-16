# When an exported name comes from different modules, raise an error.

#[NoImplicitPrelude]
import [
    Tests/Modules/Conflicts2/Lib3,
]


main():
    ()

# expected exit status: 101
# expected stderr:
# Tests/Modules/Conflicts2/Lib3 exports multiple Foos:
# Tests/Modules/Conflicts2/Lib2/Foo
# Tests/Modules/Conflicts2/Lib1/Foo
