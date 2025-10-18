import [Compiler/Error]


#[derive(ToDoc)]
type TypeError(
    loc: Loc,
    msg: Str,
)


impl ToDoc[TypeError]:
    toDoc(self: TypeError) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("loc =") + Doc.nested(4, Doc.break_(1) + self.loc.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("msg =") + Doc.nested(4, Doc.break_(1) + self.msg.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TypeError") + Doc.char('(') + args)
