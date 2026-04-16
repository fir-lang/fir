# A plain import imports everything exported from the imported module. Imported
# things are used directly (no prefix).
#
# To avoid exporting an imported definition, rename it with a `_` prefix.


#[NoImplicitPrelude]
import [Tests/Modules/DefaultImportsHiding/Lib1]


main():
    lib1Fun()
    lib2Fun()

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/Modules/DefaultImportsHiding/Main.fir:13:5: Unbound name lib2Fun
