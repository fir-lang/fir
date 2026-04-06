trait Foo[t]:
    type RecRow: Row[Rec]

impl Foo[U32]:
    type RecRow = Str

# expected exit status: 101
# expected stderr:
# tests/AssocTyKindsFail.fir:5:10: Associated type RecRow is expected to have kind Row[Rec], but has kind *
