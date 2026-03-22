type Synonym = U32

trait Foo[c]:
    get(self: c) U32

impl Foo[U32]:
    get(self: U32) Synonym:
        self

# args: --typecheck
