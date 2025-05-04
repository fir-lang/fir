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

        Expr.Str(parts):
            let doc = Doc.char('"')
            for part: StrPart in parts.iter():
                match part:
                    StrPart.Str(str):
                        # TODO: Escapes
                        doc = doc.cat(Doc.str(str))
                    StrPart.Expr(expr):
                        doc = doc.cat(Doc.char('`')).cat(expr.node.pprint()).cat(Doc.char('`'))
            doc

        Expr.Char(char):
            # TODO: Escapes
            Doc.char('\'').cat(Doc.char(char)).cat(Doc.char('\''))

        Expr.Self:
            Doc.str("self")

        Expr.BinOp(BinOpExpr(left, right, op)):
            # TODO: Precedence and parens
            # TODO: Operator string
            left.node.pprint() \
                .cat(Doc.blank(1)) \
                .cat(Doc.str(op.toStr())) \
                .cat(Doc.blank(1)) \
                .cat(right.node.pprint())

        Expr.UnOp(UnOpExpr(op, expr)):
            let opChar = match op:
                UnOp.Not: '!'
                UnOp.Neg: '-'
            Doc.char(opChar).cat(expr.node.pprint())

        Expr.Record(fields):
            _ppParenNamedFields(fields)

        Expr.Variant(VariantExpr(id, args)):
            Doc.char('[').cat(Doc.str(id.name)).cat(_ppParenNamedFields(args)).cat(Doc.char(']'))

        Expr.Return(expr):
            Doc.str("return ").cat(expr.node.pprint())

        Expr.Match(MatchExpr(scrutinee, alts)):
            Doc.str("match ").cat(scrutinee.node.pprint()).cat(Doc.char(':')).cat(Doc.hardLine()) \
                .cat(interleave(alts.iter().map(_ppAlt), Doc.hardLine())) \
                .cat(Doc.hardLine())

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

_ppParenNamedFields(fields: Vec[Named[L[Expr]]]): Doc
    Doc.char('(').cat(interleave(fields.iter().map(_ppNamedArg), Doc.str(", "))).cat(Doc.char(')'))

_ppNamedArg(arg: Named[L[Expr]]): Doc
    let doc = match arg.name:
        Option.Some(name):
            Doc.str(name.name).cat(Doc.str(" = "))
        Option.None:
            Doc.empty()
    doc.cat(arg.node.node.pprint())

_ppAlt(alt: Alt): Doc
    panic("TODO")

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
