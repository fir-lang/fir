type Synonym = U32

trait Foo[c]:
    get(self: c) Synonym

impl Foo[U32]:
    get(self: U32) U32:
        self

# args: --typecheck
