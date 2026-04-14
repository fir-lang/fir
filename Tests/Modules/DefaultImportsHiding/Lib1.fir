#[NoImplicitPrelude]
import [Tests/Modules/DefaultImportsHiding/Lib2/[lib2Fun as _lib2Fun]]


lib1Fun():
    _lib2Fun()
