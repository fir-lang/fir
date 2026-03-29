type Box[recRowR: Row[Rec]](inner: (..recRowR))

identity(b: Box[r]) Box[row(..r)]:
    b

# args: --typecheck
