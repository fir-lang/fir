Expr.pprint(self): Doc
    match self:
        Expr.Var(VarExpr(id, tyArgs)) | Expr.Constr(ConstrExpr(id, tyArgs)):
            Doc.str(id.name) + _ppTyArgs(tyArgs)

        Expr.ConstrSelect(ConstrSelectExpr(ty, constr, tyArgs)):
            Doc.str(ty.name) + Doc.char('.') + Doc.str(constr.name) + _ppTyArgs(tyArgs)

        Expr.FieldSelect(FieldSelectExpr(object, field)):
            let addParens = _needsParens(object.node)
            let doc = object.node.pprint()
            if addParens:
                doc = parens(doc)
            doc + Doc.char('.') + Doc.str(field.name)

        Expr.MethodSelect(MethodSelectExpr(object, method, ..)):
            # TODO: Print all of the details.
            let addParens = _needsParens(object.node)
            let doc = object.node.pprint()
            if addParens:
                doc = parens(doc)
            doc + Doc.char('.') + Doc.str(method.name)

        Expr.AssocFnSelect(AssocFnSelectExpr(ty, member, tyArgs)):
            Doc.str(ty.name) + Doc.char('.') + Doc.str(member.name) + _ppTyArgs(tyArgs)

        Expr.Call(CallExpr(fun, args)):
            let addParens = _needsParens(fun.node)
            let doc = fun.node.pprint()
            if addParens:
                doc = parens(doc)
            doc + parens(join(args.iter().map(CallArg.pprint), Doc.str(", ")))

        Expr.Int(IntExpr(text, ..)):
            # TODO: Print all of the details
            Doc.str(text)

        Expr.Str(parts):
            let doc = Doc.char('"')
            for part: StrPart in parts.iter():
                match part:
                    StrPart.Str(str):
                        # TODO: Escapes
                        doc += Doc.str(str)
                    StrPart.Expr(expr):
                        doc += Doc.char('`') + expr.node.pprint() + Doc.char('`')
            doc

        Expr.Char(char):
            # TODO: Escapes
            Doc.char('\'') + Doc.char(char) + Doc.char('\'')

        Expr.Self:
            Doc.str("self")

        Expr.BinOp(BinOpExpr(left, right, op)):
            # TODO: Precedence and parens
            # TODO: Operator string
            parens(left.node.pprint()) \
                + Doc.blank(1) \
                + Doc.str(op.toStr()) \
                + Doc.blank(1) \
                + parens(right.node.pprint())

        Expr.UnOp(UnOpExpr(op, expr)):
            let opChar = match op:
                UnOp.Not: '!'
                UnOp.Neg: '-'
            Doc.char(opChar) + expr.node.pprint()

        Expr.Record(fields):
            _ppNamedList(fields, Expr.pprint)

        Expr.Variant(VariantExpr(id, args)):
            brackets(Doc.str(id.name) + _ppNamedList(args, Expr.pprint))

        Expr.Return(expr):
            Doc.str("return ") + expr.node.pprint()

        Expr.Match(MatchExpr(scrutinee, alts)):
            Doc.str("match ") + scrutinee.node.pprint() + Doc.char(':') + Doc.hardLine() \
                + join(alts.iter().map(_ppAlt), Doc.hardLine()) \
                + Doc.hardLine()

        Expr.If(IfExpr(branches, else_branch)):
            let doc = _ppIfBranch("if", branches.get(0).guard, branches.get(0).body)
            for branch: (guard: L[Expr], body: Vec[L[Stmt]]) in branches.iter().skip(1):
                doc += _ppIfBranch("elif", branch.guard, branch.body)
            if else_branch is Option.Some(stmts):
                for stmt: L[Stmt] in stmts.iter():
                    doc += stmt.node.pprint() + Doc.hardLine()
            doc

        Expr.Fn_(FnExpr(sig, body, ..)):
            panic("Expr.Fn_")

        Expr.Is(IsExpr(expr, pat)):
            expr.node.pprint() + Doc.str(" is ") + pat.node.pprint()

Type.pprint(self): Doc
    match self:
        Type.Named(NamedType(name, args)):
            Doc.str(name.name) + _ppTyArgs(args)

        Type.Var(var_):
            Doc.str(var_.name)

        Type.Record(fields, extension):
            let doc = _ppNamedList(fields, Type.pprint)
            if extension is Option.Some(extension):
                if fields.len() == 0:
                    doc = Doc.str("..")
                else:
                    doc += Doc.str(", ..") + Doc.str(extension.name)
            parens(doc)

        Type.Variant(alts, extension):
            let doc = join(alts.iter().map(_ppVariantAlt), Doc.str(", "))
            if extension is Option.Some(extension):
                if alts.len() == 0:
                    doc = Doc.str("..")
                else:
                    doc += Doc.str(", ..") + Doc.str(extension.name)
            doc

        Type.Fn_(fnType): panic("")

CallArg.pprint(self): Doc
    let doc = match self.name:
        Option.Some(name): Doc.str(name.name) + Doc.str(" = ")
        Option.None: Doc.empty()
    doc + self.expr.node.pprint()

Stmt.pprint(self): Doc
    match self:
        Stmt.Let(LetStmt(lhs, ty, rhs)):
            let doc = Doc.str("let ") + lhs.node.pprint()
            if ty is Option.Some(ty):
                doc += Doc.str(": ") + ty.node.pprint()
            doc += Doc.str(" = ")
            doc + rhs.node.pprint()

        Stmt.Assign(AssignStmt(lhs, rhs, op)):
            lhs.node.pprint() + Doc.blank(1) + op.pprint() + Doc.blank(1) + rhs.node.pprint()

        Stmt.Expr(expr): expr.pprint()

        Stmt.For(ForStmt(label, pat, astTy, tcTy = _, expr, exprTy = _, body)):
            let doc = Doc.empty()

            if label is Option.Some(label):
                doc += Doc.str(label.name) + Doc.str(": ")

            doc += Doc.str("for ") + pat.node.pprint()

            if astTy is Option.Some(astTy):
                doc += Doc.str(": ") + astTy.node.pprint()

            doc += Doc.str(" in ") + expr.node.pprint() + Doc.char(':') + Doc.hardLine()
            doc += _ppStmts(body)
            doc.nest(4)

        Stmt.While(WhileStmt(label, cond, body)):
            let doc = Doc.empty()

            if label is Option.Some(label):
                doc += Doc.str(label.name) + Doc.str(": ")

            doc += Doc.str("while ") + cond.node.pprint() + Doc.str(": ") + Doc.hardLine()
            doc += _ppStmts(body)
            doc.nest(4)

        Stmt.Break(label, level = _):
            let doc = Doc.str("break")
            if label is Option.Some(label):
                doc += Doc.blank(1) + Doc.str(label.name)
            doc

        Stmt.Continue(label, level = _):
            let doc = Doc.str("continue")
            if label is Option.Some(label):
                doc += Doc.blank(1) + Doc.str(label.name)
            doc

Pat.pprint(self): Doc
    match self:
        Pat.Var(VarPat(var_, ty)):
            Doc.str(var_.name)

        Pat.Constr(ConstrPat(constr, fields, tyArgs)):
            let doc = Doc.str(constr.type_.name)
            if constr.constr is Option.Some(constr):
                doc += Doc.char('.') + Doc.str(constr.name)
            doc + parens(_ppNamedList(fields, Pat.pprint))

        Pat.Variant(VariantPat(constr, fields)):
            Doc.char('~') + Doc.str(constr.name) + parens(_ppNamedList(fields, Pat.pprint))

        Pat.Record(fields):
            _ppNamedList(fields, Pat.pprint)

        Pat.Ignore:
            Doc.char('_')

        Pat.Str(str):
            # TODO: Escapes
            Doc.char('"') + Doc.str(str) + Doc.char('"')

        Pat.Char(char):
            # TODO: Escapes
            Doc.char('\'') + Doc.char(char) + Doc.char('\'')

        Pat.StrPfx(str, var_):
            Pat.Str(str).pprint() + Doc.blank(1) + Doc.str(var_.name)

        Pat.Or(pat1, pat2):
            parens(pat1.node.pprint() + Doc.str(" | ") + pat2.node.pprint())

AssignOp.pprint(self): Doc
    match self:
        AssignOp.Eq: Doc.str("=")
        AssignOp.PlusEq: Doc.str("+=")
        AssignOp.MinusEq: Doc.str("-=")
        AssignOp.StarEq: Doc.str("*=")
        AssignOp.CaretEq: Doc.str("^=")

FunSig.pprint(self): Doc
    let doc = Doc.empty()
    if self.context.preds.len() != 0:
        doc += brackets(
            commaSep(self.context.preds.iter().map(fn(ty: L[Type]) { ty.node.pprint() })))

    let argList = Doc.empty()
    let firstArg = Bool.True

    match self.self_:
        SelfParam.No: ()
        SelfParam.Implicit: argList += Doc.str("self")
        SelfParam.Explicit(ty): argList += Doc.str("self: ") + ty.node.pprint()

    for param: (name: Id, ty: L[Type]) in self.params.iter():
        argList += Doc.str(", ") + Doc.str(param.name.name) + Doc.str(": ") + param.ty.node.pprint()

    doc += parens(argList)

    if self.exceptions is Option.Some(_) || self.returnTy is Option.Some(_):
        doc += Doc.str(":")

    if self.exceptions is Option.Some(ty):
        doc += Doc.blank(1) + ty.node.pprint()

    if self.returnTy is Option.Some(ty):
        doc += Doc.blank(1) + ty.node.pprint()

    doc

_ppTyArgs(args: Vec[L[Type]]): Doc
    if args.len() == 0:
        return Doc.empty()

    brackets(commaSep(
        args.iter().map(fn(l: L[Type]): Doc { l.node.pprint() })))

_ppNamedList(namedList: Vec[Named[L[a]]], ppItem: Fn(a): exn Doc): exn Doc
    parens(commaSep(
        namedList.iter().map(fn(a: Named[L[a]]): Doc { _ppNamed(a, ppItem) })))

_ppNamed(named: Named[L[a]], ppItem: Fn(a): exn Doc): exn Doc
    let doc = match named.name:
        Option.Some(name):
            Doc.str(name.name) + Doc.str(" = ")
        Option.None:
            Doc.empty()
    doc + ppItem(named.node.node)

_ppAlt(alt: Alt): Doc
    let doc = alt.pattern.node.pprint()
    if alt.guard is Option.Some(guard):
        panic("TODO")
    doc += Doc.char(':') + Doc.hardLine() + _ppStmts(alt.rhs)
    doc.nest(4)

_ppStmts(stmts: Vec[L[Stmt]]): Doc
    joinTrailing(
        stmts.iter().map(fn(stmt: L[Stmt]): Doc { stmt.node.pprint() }),
        Doc.hardLine())

_ppIfBranch(prefix: Str, guard: L[Expr], body: Vec[L[Stmt]]): Doc
    let doc = Doc.str(prefix) \
        + Doc.break_(1) \
        + guard.node.pprint() \
        + Doc.char(':') \
        + Doc.hardLine()

    for stmt: L[Stmt] in body.iter():
        doc += stmt.node.pprint() + Doc.hardLine()
        
    doc

_ppVariantAlt(alt: VariantAlt): Doc
    let doc = Doc.str(alt.con.name)
    if alt.fields.len() != 0:
        doc += _ppNamedList(alt.fields, Type.pprint)
    doc

_needsParens(expr: Expr): Bool
    expr is Expr.BinOp(_) | Expr.UnOp(_) | Expr.Return(_) | Expr.Match(_) | \
                Expr.If(_) | Expr.Fn_(_)

commaSep[Iterator[iter, Doc, exn]](iter: iter): exn Doc
    join(iter, Doc.str(", "))

join[Iterator[iter, Doc, exn]](iter: iter, sep: Doc): exn Doc
    let doc: Doc = match iter.next():
        Option.None: return Doc.empty()
        Option.Some(doc): doc

    for item: Doc in iter:
        doc += sep + item

    doc

joinTrailing[Iterator[iter, Doc, exn]](iter: iter, sep: Doc): exn Doc
    join(iter, sep) + sep

parens(doc: Doc): Doc
    Doc.char('(') + doc + Doc.char(')')

brackets(doc: Doc): Doc
    Doc.char('[') + doc + Doc.char(']')
