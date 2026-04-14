# Test that a local type synonym can reference a same-named type in another
# module via a prefix, without causing a false cycle.

#[NoImplicitPrelude]
import [Tests/Modules/SynonymPrefix/Lib as Lib]

type MyType = Lib/MyType

# args: --typecheck
