Expr.pprint(self): Doc
    match self:
        Expr.Var(VarExpr(id, tyArgs)) | Expr.Constr(ConstrExpr(id, tyArgs)):
            Doc.str(id.name).cat(_ppTyArgs(tyArgs))

        Expr.ConstrSelect(ConstrSelectExpr(ty, constr, tyArgs)):
            Doc.str(ty.name).cat(Doc.char('.')).cat(Doc.str(constr.name)).cat(_ppTyArgs(tyArgs))

        Expr.FieldSelect(FieldSelectExpr(object, field)):
            let addParens = _needsParens(object.node)
            let doc = object.node.pprint()
            if addParens:
                doc = parens(doc)
            doc.cat(Doc.char('.')).cat(Doc.str(field.name))

        Expr.MethodSelect(MethodSelectExpr(object, method, ..)):
            # TODO: Print all of the details.
            let addParens = _needsParens(object.node)
            let doc = object.node.pprint()
            if addParens:
                doc = parens(doc)
            doc.cat(Doc.char('.')).cat(Doc.str(method.name))

        Expr.AssocFnSelect(AssocFnSelectExpr(ty, member, tyArgs)):
            Doc.str(ty.name).cat(Doc.char('.')).cat(Doc.str(member.name)).cat(_ppTyArgs(tyArgs))

        Expr.Call(CallExpr(fun, args)):
            let addParens = _needsParens(fun.node)
            let doc = fun.node.pprint()
            if addParens:
                doc = parens(doc)
            doc.cat(parens(interleave(args.iter().map(CallArg.pprint), Doc.str(", "))))

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
            parens(left.node.pprint()) \
                .cat(Doc.blank(1)) \
                .cat(Doc.str(op.toStr())) \
                .cat(Doc.blank(1)) \
                .cat(parens(right.node.pprint()))

        Expr.UnOp(UnOpExpr(op, expr)):
            let opChar = match op:
                UnOp.Not: '!'
                UnOp.Neg: '-'
            Doc.char(opChar).cat(expr.node.pprint())

        Expr.Record(fields):
            _ppParenNamedFields(fields)

        Expr.Variant(VariantExpr(id, args)):
            brackets(Doc.str(id.name).cat(_ppParenNamedFields(args)))

        Expr.Return(expr):
            Doc.str("return ").cat(expr.node.pprint())

        Expr.Match(MatchExpr(scrutinee, alts)):
            Doc.str("match ").cat(scrutinee.node.pprint()).cat(Doc.char(':')).cat(Doc.hardLine()) \
                .cat(interleave(alts.iter().map(_ppAlt), Doc.hardLine())) \
                .cat(Doc.hardLine())

        Expr.If(IfExpr(branches, else_branch)):
            let doc = _ppIfBranch("if", branches.get(0).guard, branches.get(0).body)
            for branch: (guard: L[Expr], body: Vec[L[Stmt]]) in branches.iter().skip(1):
                doc = doc.cat(_ppIfBranch("elif", branch.guard, branch.body))
            match else_branch:
                Option.None: ()
                Option.Some(stmts):
                    for stmt: L[Stmt] in stmts.iter():
                        doc = doc.cat(stmt.node.pprint()).cat(Doc.hardLine())
            doc

        Expr.Fn_(FnExpr(sig, body, ..)):
            panic("Expr.Fn_")

Type.pprint(self): Doc
    match self:
        Type.Named(NamedType(name, args)):
            Doc.str(name.name).cat(_ppTyArgs(args))

        Type.Var(var_):
            Doc.str(var_.name)

        Type.Record(fields, extension):
            let doc = _ppNamedList(fields, Type.pprint)
            match extension:
                Option.None: ()
                Option.Some(extension):
                    if fields.len() == 0:
                        doc = Doc.str("..")
                    else:
                        doc = doc.cat(Doc.str(", .."))
            parens(doc)

        Type.Variant(alts, extension): panic("")

        Type.Fn_(fnType): panic("")

CallArg.pprint(self): Doc
    panic("TODO")

Stmt.pprint(self): Doc
    panic("TODO")

_ppTyArgs(args: Vec[L[Type]]): Doc
    if args.len() == 0:
        return Doc.empty()

    brackets(commaSep(
        args.iter().map(fn(l: L[Type]): Doc { l.node.pprint() })))

_ppParenNamedFields(fields: Vec[Named[L[Expr]]]): Doc
    _ppNamedList(fields, Expr.pprint)

_ppNamedArg(arg: Named[L[Expr]]): Doc
    _ppNamed(arg, Expr.pprint)

_ppNamedList(namedList: Vec[Named[L[a]]], ppItem: Fn(a): exn Doc): exn Doc
    parens(commaSep(
        namedList.iter().map(fn(a: Named[L[a]]): Doc { _ppNamed(a, ppItem) })))

_ppNamed(named: Named[L[a]], ppItem: Fn(a): exn Doc): exn Doc
    let doc = match named.name:
        Option.Some(name):
            Doc.str(name.name).cat(Doc.str(" = "))
        Option.None:
            Doc.empty()
    doc.cat(ppItem(named.node.node))

_ppAlt(alt: Alt): Doc
    panic("TODO")

_ppIfBranch(prefix: Str, guard: L[Expr], body: Vec[L[Stmt]]): Doc
    let doc = Doc.str(prefix) \
        .cat(Doc.break_(1)) \
        .cat(guard.node.pprint()) \
        .cat(Doc.char(':')) \
        .cat(Doc.hardLine())

    for stmt: L[Stmt] in body.iter():
        doc = doc.cat(stmt.node.pprint()).cat(Doc.hardLine())
        
    doc

_needsParens(expr: Expr): Bool
    match expr:
        Expr.BinOp(_) | Expr.UnOp(_) | Expr.Return(_) | Expr.Match(_) | \
            Expr.If(_) | Expr.Fn_(_): Bool.True

        _: Bool.False

commaSep[Iterator[iter, Doc, exn]](iter: iter): exn Doc
    interleave(iter, Doc.str(", "))

interleave[Iterator[iter, Doc, exn]](iter: iter, sep: Doc): exn Doc
    let doc: Doc = match iter.next():
        Option.None: return Doc.empty()
        Option.Some(doc): doc

    for item: Doc in iter:
        doc = doc.cat(sep).cat(item)

    doc

parens(doc: Doc): Doc
    Doc.char('(').cat(doc).cat(Doc.char(')'))

brackets(doc: Doc): Doc
    Doc.char('[').cat(doc).cat(Doc.char(']'))
