type Box[recRowR: Row[Rec]](inner: (..recRowR))

identity[RecRow[r]](b: Box[r]) Box[row(..r)]:
    b

# args: --typecheck
