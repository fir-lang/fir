#[NoImplicitPrelude]
import [Tests/Modules/SynonymCycle/ModB as B]

type Foo = B/Bar

# args: --typecheck
# expected exit status: 101
# expected stderr: Type synonym cycle detected: Foo, Bar
