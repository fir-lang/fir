# When a name is imported from multiple modules an error should be reported at
# the use site.

#[NoImplicitPrelude]
import [
    Tests/Modules/Conflicts1/Lib1,
    Tests/Modules/Conflicts1/Lib2,
]


main():
    let x = T1.C
    ()

# expected exit status: 101
# expected stderr:
# Tests/Modules/Conflicts1/Main.fir:12:13: Name T1 imported from multiple modules:
# - Tests/Modules/Conflicts1/Lib2
# - Tests/Modules/Conflicts1/Lib1
