# Defines a synonym whose body uses a module prefix (`Lib/`). The prefix is
# meaningful here, but downstream consumers that don't import `Lib` aliased
# can't resolve the prefix in their own env.

import [Tests/Modules/SynonymPrefixedBody/Lib as Lib]


type Bar = Lib/Foo[U32]


makeBar() Bar:
    Lib/mkFoo(u32(7))
