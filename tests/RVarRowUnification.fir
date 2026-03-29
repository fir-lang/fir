type Box[recRowR](inner: (..recRowR))

identity(b: Box[r]) Box[row(..r)]:
    b

# args: --typecheck
