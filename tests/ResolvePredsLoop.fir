# Bug repro: `ToDoc[A[t]]` impl has subgoal `ToDoc[B[t]]`, which has subgoal
# `ToDoc[A[t]]`, but with different (fresh) `UVar`. The goals are never
# recognized as already-seen because of the fresh `UVar`s, so the goal list
# grows without bound.

type A[t]:
    A1(B[t])
    A2(U32)


type B[t]:
    B1(A[t])
    B2(U32)


impl[ToDoc[B[t]], ToDoc[U32]] ToDoc[A[t]]:
    toDoc(self: A[t]) Doc:
        match self:
            A.A1(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("A.A1") + Doc.char('(') + args)
            A.A2(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("A.A2") + Doc.char('(') + args)


impl[ToDoc[A[t]], ToDoc[U32]] ToDoc[B[t]]:
    toDoc(self: B[t]) Doc:
        match self:
            B.B1(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("B.B1") + Doc.char('(') + args)
            B.B2(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("B.B2") + Doc.char('(') + args)


mk[ToDoc[A[t]], ToDoc[B[t]]](x: U32) A[t]:
    A.A2(x)


main():
    print(mk(u32(1)).toDoc().render(80))


# expected stdout: A.A2(1)
