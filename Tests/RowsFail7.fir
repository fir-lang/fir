type Foo = row[U32]

test() (x: U32, ..Foo):
    panic("")

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/RowsFail7.fir:3:19: Record extension type Foo has kind Row[Var]
