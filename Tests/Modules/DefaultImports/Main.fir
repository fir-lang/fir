# A plain import imports everything exported from the imported module. Imported
# things are used directly (no prefix).


#[NoImplicitPrelude]
import [Tests/Modules/DefaultImports/Lib1]


main():
    lib1Fun()
    lib2Fun()


# args: --typecheck
