Expr.pprint(self): Doc
    match self:
        Expr.Var(VarExpr(id, tyArgs)) | Expr.Constr(ConstrExpr(id, tyArgs)):
            Doc.str(id.name).cat(_ppTyArgs(tyArgs))

        Expr.ConstrSelect(ConstrSelectExpr(ty, constr, tyArgs)):
            Doc.str(ty.name).cat(Doc.char('.')).cat(Doc.str(constr.name)).cat(_ppTyArgs(tyArgs))

        Expr.FieldSelect(FieldSelectExpr(object, field)):
            let parens = _needsParens(object.node)
            let doc = object.node.pprint()
            if parens:
                doc = Doc.char('(').cat(doc).cat(Doc.char(')'))
            doc.cat(Doc.char('.')).cat(Doc.str(field.name))

        Expr.MethodSelect(MethodSelectExpr(object, method, ..)):
            # TODO: Print all of the details.
            let parens = _needsParens(object.node)
            let doc = object.node.pprint()
            if parens:
                doc = Doc.char('(').cat(doc).cat(Doc.char(')'))
            doc.cat(Doc.char('.')).cat(Doc.str(method.name))

        Expr.AssocFnSelect(AssocFnSelectExpr(ty, member, tyArgs)):
            Doc.str(ty.name).cat(Doc.char('.')).cat(Doc.str(member.name)).cat(_ppTyArgs(tyArgs))

        Expr.Call(CallExpr(fun, args)):
            let parens = _needsParens(fun.node)
            let doc = fun.node.pprint()
            if parens:
                doc = Doc.char('(').cat(doc).cat(Doc.char(')'))
            doc.cat(Doc.char('(')).cat(interleave(args.iter().map(CallArg.pprint), Doc.str(", "))).cat(Doc.char(')'))

        Expr.Int(IntExpr(text, ..)):
            # TODO: Print all of the details
            Doc.str(text)

        Expr.Str(_):
            panic("Expr.Str")

        Expr.Char(_):
            panic("Expr.Char")

        Expr.Self:
            panic("Expr.Self")

        Expr.BinOp(_):
            panic("Expr.BinOp")

        Expr.UnOp(_):
            panic("Expr.UnOp")

        Expr.Record(_):
            panic("Expr.Record")

        Expr.Variant(_):
            panic("Expr.Variant")

        Expr.Return(_):
            panic("Expr.Return")

        Expr.Match(_):
            panic("Expr.Match")

        Expr.If(_):
            panic("Expr.If")

        Expr.Fn_(_):
            panic("Expr.Fn_")

Type.pprint(self): Doc
    panic("TODO")

CallArg.pprint(self): Doc
    panic("TODO")

_ppTyArgs(args: Vec[L[Type]]): Doc
    if args.len() == 0:
        return Doc.empty()

    Doc.char('[') \
        .cat(interleave(args.iter().map(fn(l: L[Type]): Doc { l.node.pprint() }), Doc.str(", "))) \
        .cat(Doc.char(']'))

_needsParens(expr: Expr): Bool
    match expr:
        Expr.BinOp(_) | Expr.UnOp(_) | Expr.Return(_) | Expr.Match(_) | \
            Expr.If(_) | Expr.Fn_(_): Bool.True

        _: Bool.False

interleave[Iterator[iter, Doc, exn]](iter: iter, sep: Doc): exn Doc
    let doc: Doc = match iter.next():
        Option.None: return Doc.empty()
        Option.Some(doc): doc

    for item: Doc in iter:
        doc = doc.cat(sep).cat(item)

    doc
