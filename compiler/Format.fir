import Error
import Grammar
import Scanner

main(args: Array[Str]):
    if args.len() != 2:
        showUsageAndExit()

    let path = args.get(1)
    let fileContents = readFileUtf8(path)

    let (tokens, error) = tokenize(path, fileContents)
    if error is Option.Some(error):
        print("ERROR: `error.loc.line + 1`:`error.loc.col + 1`: `error.msg`")

    let tokens = match try(||: scan[row[]](tokens)):    # Explicitly close the variant (issue #49).
        Result.Err(~ScannerError(line, col, msg)):
            panic("`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens):
            tokens

    let parserState = ParserState.new(tokens)

    let tree = match try(||: module(parserState)):
        Result.Err(cursor):
            if cursor == tokens.len():
                panic("Parse error: unexpected end of input")
            else:
                panic("Parse error: unexpected token `tokens.get(cursor)`")
        Result.Ok(tree):
            tree

    print(formatModule(tree, tokens).render(80))


showUsageAndExit() a:
    panic("USAGE: fir format <file>")


formatModule(mod: Vec[TopDecl], tokens: Vec[Token]) Doc:
    join(mod.iter().map(|decl: TopDecl|: decl.format(tokens)), Doc.hardLine() + Doc.hardLine())


# --------------------------------------------------------------------------------------------------
# Declarations


TopDecl.format(self, tokens: Vec[Token]) Doc:
    match self:
        TopDecl.Type(d): d.format(tokens)
        TopDecl.Fun(d): d.format(tokens)
        TopDecl.Import(d): d.format(tokens)
        TopDecl.Trait(d): d.format(tokens)
        TopDecl.Impl(d): d.format(tokens)


TypeDecl.format(self, tokens: Vec[Token]) Doc:
    let doc = Doc.str("type ") + Doc.str(idText(self.name, tokens))

    if not self.typeParams.isEmpty():
        # Top-level declarations always start at column 0, and I don't think it'll be common to have
        # so many type parameters the parameter list will need line breaks. For now print the header
        # in one line.
        doc += Doc.char('[')
            + join(self.typeParams.iter().map(|id: Id|: Doc.str(idText(id, tokens))), Doc.str(", "))
            + Doc.char(']')

    if self.rhs is Option.Some(rhs):
        doc = Doc.nested(4, doc + rhs.format(tokens))

    doc


TypeDeclRhs.format(self, tokens: Vec[Token]) Doc:
    match self:
        TypeDeclRhs.Sum(decls):
            Doc.char(':')
                + Doc.hardLine()
                + join(decls.iter().map(|decl: ConDecl|: decl.format(tokens)), Doc.hardLine())
                + Doc.hardLine()

        TypeDeclRhs.Product(fields):
            fields.format(tokens)


ConDecl.format(self, tokens: Vec[Token]) Doc:
    Doc.str(idText(self.name, tokens)) + self.fields.format(tokens)


ConFields.format(self, tokens: Vec[Token]) Doc:
    match self:
        ConFields.Empty:
            Doc.empty()

        ConFields.Named(fields):
            let doc = Doc.char('(') + Doc.break_(0)

            let fieldIdx: U32 = 0
            for field: (name: Id, ty: Type) in fields.iter():
                if fieldIdx != 0:
                    doc += Doc.char(',') + Doc.break_(1)
                fieldIdx += 1

                doc +=
                    Doc.str(idText(field.name, tokens))
                        + Doc.str(": ")
                        + field.ty.format(tokens)

            if fields.len() != 0:
                doc += Doc.whenNotFlat(Doc.char(','))

            Doc.grouped(doc.nest(4) + Doc.break_(0) + Doc.char(')'))

        ConFields.Unnamed(fields):
            let doc = Doc.char('(') + Doc.break_(0)

            let fieldIdx: U32 = 0
            for field: Type in fields.iter():
                if fieldIdx != 0:
                    doc += Doc.char(',') + Doc.break_(1)
                fieldIdx += 1

                doc += field.format(tokens)

            if fields.len() != 0:
                doc += Doc.whenNotFlat(Doc.char(','))

            Doc.grouped(doc.nest(4) + Doc.break_(0) + Doc.char(')'))


FunDecl.format(self, tokens: Vec[Token]) Doc:
    let doc = match self.parentTy:
        Option.Some(id):
            Doc.str(idText(id, tokens)) + Doc.char('.')
        Option.None:
            Doc.empty()

    doc += Doc.str(idText(self.name, tokens))

    if not self.sig.context.preds.isEmpty():
        doc +=
            Doc.char('[')
                + join(self.sig.context.preds.iter().map(|ty: Type|: ty.format(tokens)), Doc.str(", "))
                + Doc.char(']')

    doc += Doc.char('(')

    let argIdx: U32 = 0
    for arg: (name: Id, ty: Option[Type]) in self.sig.params.iter():
        if argIdx != 0:
            doc += Doc.char(',') + Doc.break_(1)
        argIdx += 1

        doc += Doc.str(idText(arg.name, tokens))

        if arg.ty is Option.Some(ty):
            doc += Doc.str(": ") + ty.format(tokens)

    if self.sig.params.len() != 0:
        doc += Doc.whenNotFlat(Doc.char(','))

    if self.sig.returnTy is Option.Some(ret):
        doc += Doc.blank(1) + ret.format(tokens)

    if self.sig.exceptions is Option.Some(exn):
        doc += Doc.blank(1) + exn.format(tokens)

    if self.body is Option.Some(stmts):
        doc += Doc.char(':') + Doc.hardLine() + formatStmts(stmts, tokens)
        doc = Doc.nested(4, doc)

    doc


ImportDecl.format(self, tokens: Vec[Token]) Doc:
    Doc.str("import ") + join(self.path.iter().map(Doc.str), Doc.char('.'))


TraitDecl.format(self, tokens: Vec[Token]) Doc:
    Doc.nested(
        4,
        Doc.str("trait ") + Doc.str(idText(self.name, tokens))
            + Doc.char('[')
            + join(self.typeParams.iter().map(|id: Id|: Doc.str(idText(id,tokens))), Doc.str(", "))
            + Doc.str("]:")
            + Doc.hardLine()
            + join(self.items.iter().map(|decl: FunDecl|: decl.format(tokens)), Doc.hardLine() + Doc.hardLine()))


ImplDecl.format(self, tokens: Vec[Token]) Doc:
    let doc = Doc.str("impl")

    if not self.context.preds.isEmpty():
        doc += Doc.char('[')

        let predIdx: U32 = 0
        for pred: Type in self.context.preds.iter():
            if predIdx != 0:
                doc += Doc.char(',') + Doc.break_(1)
            predIdx += 1

            doc += pred.format(tokens)

        doc += Doc.char(']')

    doc +=
        Doc.blank(1)
            + Doc.str(idText(self.trait_, tokens))
            + Doc.char('[')

    let tyIdx: U32 = 0
    for ty: Type in self.tys.iter():
        if tyIdx != 0:
            doc += Doc.char(',') + Doc.break_(1)
        tyIdx += 1

        doc += ty.format(tokens)

    doc += Doc.char(']') + Doc.char(':') + Doc.hardLine()

    doc += join(
        self.items.iter().map(|decl: FunDecl|: decl.format(tokens)),
        Doc.hardLine()
    )

    doc.nest(4)


# --------------------------------------------------------------------------------------------------
# Expressions


Expr.format(self, tokens: Vec[Token]) Doc:
    match self:
        Expr.Var(e): e.format(tokens)
        Expr.ConstrSelect(e): e.format(tokens)
        Expr.FieldSelect(e): e.format(tokens)
        Expr.AssocFnSelect(e): e.format(tokens)
        Expr.Call(e): e.format(tokens)
        Expr.Int(e): e.format(tokens)
        Expr.Str(e): e.format(tokens)
        Expr.Char(e): e.format(tokens)
        Expr.Self(e): Doc.str(tokenText(e, tokens))
        Expr.BinOp(e): e.format(tokens)
        Expr.UnOp(e): e.format(tokens)
        Expr.Record(e): e.format(tokens)
        Expr.Return(e): e.format(tokens)
        Expr.Match(e): e.format(tokens)
        Expr.If(e): e.format(tokens)
        Expr.Fn_(e): e.format(tokens)
        Expr.Is(e): e.format(tokens)
        Expr.Do(e): e.format(tokens)
        Expr.Seq(e): e.format(tokens)
        Expr.Paren(e): Doc.char('(') + e.format(tokens) + Doc.char(')')

        Expr.MethodSelect(e):
            # These expressions are intoruduced by the type checker, which we don't run when
            # formatting.
            panic("Expr.MethodSelect")


VarExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.str(idText(self.id, tokens)) + formatTyArgs(self.userTyArgs, tokens)


Constructor.format(self, tokens: Vec[Token]) Doc:
    let doc = if self.variant:
        Doc.char('~')
    else:
        Doc.empty()

    doc += Doc.str(idText(self.ty, tokens))

    if self.constr is Option.Some(con):
        doc += Doc.char('.') + Doc.str(idText(con, tokens))

    doc + formatTyArgs(self.userTyArgs, tokens)


FieldSelectExpr.format(self, tokens: Vec[Token]) Doc:
    #|
    Group sequence of selections so that we will format like one of the following:

        foo[T1].bar[t].baz[U32]

        foo[T1]
              .bar[t]
              .baz[U32]

    and not as:

        foo[T1]
              .bar[t]
                   .baz[U32]
    |#

    let selection = self
    let fields: Vec[(field: Id, tyArgs: Vec[Type])] = Vec.withCapacity(1)
    loop:
        fields.push((field = selection.field, tyArgs = selection.userTyArgs))
        if selection.object is Expr.FieldSelect(e):
            selection = e
        else:
            break

    let doc = selection.object.format(tokens)
    while fields.pop() is Option.Some((field, tyArgs)):
        doc += Doc.break_(0)
            + Doc.char('.')
            + Doc.str(idText(field, tokens))
            + formatTyArgs(tyArgs, tokens)

    doc.nest(4).group()


AssocFnSelectExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.nested(
        4,
        Doc.str(idText(self.ty, tokens))
            + Doc.break_(0)
            + Doc.char('.')
            + Doc.str(idText(self.member, tokens))
            + formatTyArgs(self.userTyArgs, tokens))
        .group()


CallExpr.format(self, tokens: Vec[Token]) Doc:
    #|
    Single line:

        f(e1, e2, e3)

    Or split:

        f(
            e1,
            e2,
            e3,
        )
    |#

    # TODO: Add parens to function when necessary.
    let doc = self.fun.format(tokens) + Doc.char('(') + Doc.break_(0)

    let argIdx: U32 = 0
    for arg: Named[Expr] in self.args.iter():
        if argIdx != 0:
            doc += Doc.char(',') + Doc.break_(1)
        argIdx += 1

        doc += formatNamed(arg, Expr.format, tokens)

    if self.args.len() != 0:
        doc += Doc.whenNotFlat(Doc.char(','))

    Doc.grouped(doc.nest(4) + Doc.break_(0) + Doc.char(')'))


IntExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.str(tokenText(self.token, tokens))


StrExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.str(tokenText(self.token, tokens))


CharExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.str(tokenText(self.token, tokens))


BinOpExpr.format(self, tokens: Vec[Token]) Doc:
    # Binary operators are all left-associative, so the right-hand side can never be a `BinOp`
    # unless it's wrapped with a `Paren`.
    #
    # When breaking print the operator before the right-hand side. Group associativity changes. For
    # example:
    #
    #     <expr1> + <expr2> * <expr3> * <expr4> + <expr5>
    #
    # Should be formatted as: (when breaking)
    #
    #     <expr1>
    #         + <expr2> * <expr3> * <expr4>
    #         + <expr5>
    #
    # Or when breaking the inner group:
    #
    #     <expr1>
    #         + <expr2>
    #             * <expr3>
    #             * <expr4>
    #         + <expr5>

    panic("TODO")


UnOpExpr.format(self, tokens: Vec[Token]) Doc:
    self.op.format() + Doc.blank(1) + self.expr.format(tokens)


UnOp.format(self) Doc:
    match self:
        UnOp.Not: Doc.str("not")
        UnOp.Neg: Doc.char('-')


RecordExpr.format(self, tokens: Vec[Token]) Doc:
    let doc = Doc.char('(')

    let fieldIdx: U32 = 0
    for field: Named[Expr] in self.fields.iter():
        if fieldIdx != 0:
            doc += Doc.char(',') + Doc.break_(1)
        fieldIdx += 1

        doc += formatNamed(field, Expr.format, tokens)

    Doc.nested(4, doc + Doc.char(')'))


ReturnExpr.format(self, tokens: Vec[Token]) Doc:
    match self.expr:
        Option.None:
            Doc.str("return")

        Option.Some(expr):
            Doc.nested(
                4,
                Doc.str("return") + Doc.break_(1) + expr.format(tokens))
                .group()


MatchExpr.format(self, tokens: Vec[Token]) Doc:
    let doc = Doc.str("match ")
        + Doc.nested(8, self.scrutinee.format(tokens))
        + Doc.char(':')

    for alt: Alt in self.alts.iter():
        doc += Doc.hardLine() + alt.format(tokens)

    doc.nest(4)


Alt.format(self, tokens: Vec[Token]) Doc:
    let doc = self.pattern.format(tokens)

    if self.guard is Option.Some(guard):
        doc += Doc.break_(1) + Doc.str("if ") + guard.format(tokens)
        doc = Doc.nested(8, doc)

    let body = formatStmts(self.rhs, tokens)

    Doc.nested(4, doc + Doc.char(':') + Doc.hardLine() + body)


IfExpr.format(self, tokens: Vec[Token]) Doc:
    let firstBranch = self.branches.get(0)
    let doc =
        Doc.nested(
            4,
            Doc.str("if ")
                + firstBranch.guard.format(tokens)
                + Doc.char(':')
                + Doc.hardLine()
                + formatStmts(firstBranch.body, tokens))

    for branch: (guard: Expr, body: Vec[Stmt]) in self.branches.iter().skip(1):
        doc += Doc.hardLine()
        doc += Doc.nested(
            4,
            Doc.str("elif ")
                + branch.guard.format(tokens)
                + Doc.char(':')
                + Doc.hardLine()
                + formatStmts(branch.body, tokens))

    if self.elseBranch is Option.Some(body):
        doc += Doc.hardLine()
        doc += Doc.nested(4, Doc.str("else:") + Doc.hardLine() + formatStmts(body, tokens))

    doc


FnExpr.format(self, tokens: Vec[Token]) Doc:
    # assert(self.sig.context.typeParams.isEmpty)
    # assert(self.sig.context.preds.isEmpty)
    # assert(self.sig.self_ is SelfParam.No)

    let doc = Doc.char('|')

    let paramIdx: U32 = 0
    for param: (name: Id, ty: Option[Type]) in self.sig.params.iter():
        if paramIdx != 0:
            doc += Doc.str(", ")
        paramIdx += 1

        doc += Doc.str(idText(param.name, tokens))
        if param.ty is Option.Some(ty):
            doc += Doc.str(": ") + ty.format(tokens)

    doc += Doc.char('|')

    if self.sig.returnTy is Option.Some(ret):
        doc += Doc.blank(1) + ret.format(tokens)

    if self.sig.exceptions is Option.Some(exn):
        doc += Doc.blank(1) + exn.format(tokens)

    doc += Doc.char(':')

    if self.body.len() > 1:
        doc += Doc.hardLine()
    else:
        doc += Doc.break_(1)

    doc += formatStmts(self.body, tokens)

    doc.nest(4)


IsExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.nested(
        4,
        self.expr.format(tokens)
            + Doc.break_(1)
            + Doc.str("is ")
            + self.pat.format(tokens))
        .group()


DoExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.nested(4, Doc.str("do:") + Doc.hardLine() + formatStmts(self.body, tokens))


SeqExpr.format(self, tokens: Vec[Token]) Doc:
    let doc = match self.ty:
        Option.None:
            Doc.char('[')
        Option.Some(ty):
            ty.format(tokens) + Doc.str(".[")

    let elemIdx: U32 = 0
    for elem: (key: Option[Expr], value: Expr) in self.elems.iter():
        if elemIdx != 0:
            doc += Doc.char(',') + Doc.break_(1)
        elemIdx += 1

        if elem.key is Option.Some(key):
            doc += key.format(tokens) + Doc.str(" =") + Doc.break_(1)

        doc += elem.value.format(tokens)

    if self.elems.len() != 0:
        doc += Doc.whenNotFlat(Doc.char(','))

    Doc.grouped(doc.nest(4) + Doc.break_(0) + Doc.char(']'))


# --------------------------------------------------------------------------------------------------
# Statements


formatStmts(stmts: Vec[Stmt], tokens: Vec[Token]) Doc:
    join(stmts.iter().map(|stmt: Stmt|: stmt.format(tokens)), Doc.hardLine())


Stmt.format(self, tokens: Vec[Token]) Doc:
    match self:
        Stmt.Let(s): s.format(tokens)
        Stmt.Assign(s): s.format(tokens)
        Stmt.Expr(s): s.format(tokens)
        Stmt.For(s): s.format(tokens)
        Stmt.While(s): s.format(tokens)
        Stmt.Loop(s): s.format(tokens)
        Stmt.Break(s): s.format(tokens)
        Stmt.Continue(s): s.format(tokens)


LetStmt.format(self, tokens: Vec[Token]) Doc:
    let doc = self.lhs.format(tokens)

    if self.ty is Option.Some(ty):
        doc += Doc.str(": ") + ty.format(tokens)

    Doc.nested(4, doc + Doc.break_(1) + self.rhs.format(tokens))


AssignStmt.format(self, tokens: Vec[Token]) Doc:
    Doc.nested(
        4,
        self.lhs.format(tokens)
            + Doc.blank(1)
            + self.op.format()
            + Doc.break_(1)
            + self.rhs.format(tokens))
        .group()


AssignOp.format(self) Doc:
    Doc.str(match self:
        AssignOp.Eq: "="
        AssignOp.PlusEq: "+="
        AssignOp.MinusEq: "-="
        AssignOp.StarEq: "*="
        AssignOp.CaretEq: "^=")


ForStmt.format(self, tokens: Vec[Token]) Doc:
    # TODO: Add loop label
    let doc = Doc.str("for ") + self.pat.format(tokens)

    if self.astTy is Option.Some(ty):
        doc += Doc.str(": ") + ty.format(tokens)

    doc += Doc.nested(
        8,
        Doc.str(" in") + Doc.break_(1) + self.expr.format(tokens) + Doc.char(':'))

    doc + Doc.hardLine() + formatStmts(self.body, tokens)


WhileStmt.format(self, tokens: Vec[Token]) Doc:
    # TODO: Add loop label
    Doc.nested(
        4,
        Doc.nested(4, Doc.str("while ") + self.cond.format(tokens))
            + Doc.hardLine()
            + formatStmts(self.body, tokens))


LoopStmt.format(self, tokens: Vec[Token]) Doc:
    Doc.nested(
        4,
        Doc.str("loop:")
            + Doc.hardLine()
            + formatStmts(self.body, tokens))


BreakStmt.format(self, tokens: Vec[Token]) Doc:
    match self.label:
        Option.None:
            Doc.str("break")

        Option.Some(label):
            Doc.nested(4, Doc.str("break") + Doc.break_(1) + Doc.str(idText(label, tokens)))


ContinueStmt.format(self, tokens: Vec[Token]) Doc:
    match self.label:
        Option.None:
            Doc.str("continue")

        Option.Some(label):
            Doc.nested(4, Doc.str("continue") + Doc.break_(1) + Doc.str(idText(label, tokens)))


# --------------------------------------------------------------------------------------------------
# Types


Type.format(self, tokens: Vec[Token]) Doc:
    match self:
        Type.Named(t): t.format(tokens)
        Type.Var(id): Doc.str(idText(id, tokens))
        Type.Record(t): t.format(tokens)
        Type.Variant(t): t.format(tokens)
        Type.Fn_(t): t.format(tokens)


NamedType.format(self, tokens: Vec[Token]) Doc:
    Doc.str(idText(self.name, tokens)) + formatTyArgs(self.args, tokens)


RecordType.format(self, tokens: Vec[Token]) Doc:
    let doc = if self.isRow:
        Doc.str("row(")
    else:
        Doc.char('(')

    let fieldIdx: U32 = 0
    for field: Named[Type] in self.fields.iter():
        if fieldIdx != 0:
            doc += Doc.char(',') + Doc.break_(1)
        fieldIdx += 1

        doc += formatNamed(field, Type.format, tokens)

    if self.extension is Option.Some(ext):
        if not self.fields.isEmpty():
            doc += Doc.str(", ..")
        else:
            doc += Doc.str("..")

        doc += Doc.str(idText(ext, tokens))

    doc + Doc.char(')')


VariantType.format(self, tokens: Vec[Token]) Doc:
    let doc = Doc.char('[')

    let altIdx: U32 = 0
    for alt: VariantAlt in self.alts.iter():
        if altIdx != 0:
            doc += Doc.str(", ")
        altIdx += 1

        doc += alt.format(tokens)

    if self.extension is Option.Some(ext):
        if not self.alts.isEmpty():
            doc += Doc.str(", ..")
        else:
            doc += Doc.str("..")

        doc += Doc.str(idText(ext, tokens))

    doc + Doc.char(']')


VariantAlt.format(self, tokens: Vec[Token]) Doc:
    let doc = Doc.str(idText(self.con, tokens))

    if not self.fields.isEmpty():
        doc += Doc.char('(') + Doc.break_(0)

        let fieldIdx: U32 = 0
        for field: Named[Type] in self.fields.iter():
            if fieldIdx != 0:
                doc += Doc.char(',') + Doc.break_(1)
            fieldIdx += 1

            doc += formatNamed(field, Type.format, tokens)

        doc = Doc.nested(4, doc) + Doc.char(')')

    doc


FnType.format(self, tokens: Vec[Token]) Doc:
    let doc =
        Doc.str("Fn(")
            + join(self.args.iter().map(|arg: Type|: arg.format(tokens)), Doc.str(", "))
            + Doc.char(')')

    if self.ret is Option.Some(ret):
        doc += Doc.blank(1) + ret.format(tokens)

    if self.exceptions is Option.Some(exn):
        doc += Doc.blank(1) + exn.format(tokens)

    doc


# --------------------------------------------------------------------------------------------------
# Patterns


Pat.format(self, tokens: Vec[Token]) Doc:
    match self:
        Pat.Var(p):
            p.format(tokens)

        Pat.Constr(p):
            p.format(tokens)

        Pat.Record(p):
            p.format(tokens)

        Pat.Ignore(p)
            | Pat.Str(_, p)
            | Pat.Char(_, p): Doc.str(tokenText(p, tokens))

        Pat.Or(p1, p2):
            Doc.nested(
                4,
                p1.format(tokens)
                    + Doc.break_(1)
                    + Doc.str("| ")
                    + p2.format(tokens))
                .group()


VarPat.format(self, tokens: Vec[Token]) Doc:
    Doc.str(idText(self.var_, tokens))


ConstrPat.format(self, tokens: Vec[Token]) Doc:
    let doc = self.constr.format(tokens)

    if not self.fields.isEmpty() or self.ignoreRest:
        doc += Doc.char('(') + Doc.break_(0)

        let fieldIdx: U32 = 0
        for field: Named[Pat] in self.fields.iter():
            if fieldIdx != 0:
                doc += Doc.char(',') + Doc.break_(1)
            fieldIdx += 1

            doc += formatNamed(field, Pat.format, tokens)

        if self.ignoreRest:
            if fieldIdx != 0:
                doc += Doc.char(',') + Doc.break_(1)

            doc += Doc.str("..")

        doc += Doc.whenNotFlat(Doc.char(','))

    Doc.grouped(doc.nest(4) + Doc.break_(0) + Doc.char(')'))


RecordPat.format(self, tokens: Vec[Token]) Doc:
    let doc = Doc.char('(') + Doc.break_(0)

    let fieldIdx: U32 = 0
    for field: Named[Pat] in self.fields.iter():
        if fieldIdx != 0:
            doc += Doc.char(',') + Doc.break_(1)
        fieldIdx += 1

        doc += formatNamed(field, Pat.format, tokens)

    if self.ignoreRest:
        if fieldIdx != 0:
            doc += Doc.char(',') + Doc.break_(1)

        doc += Doc.str("..")

    doc += Doc.whenNotFlat(Doc.char(','))

    Doc.grouped(doc.nest(4) + Doc.break_(0) + Doc.char(')'))


# --------------------------------------------------------------------------------------------------


formatTyArgs(tyArgs: Vec[Type], tokens: Vec[Token]) Doc:
    let doc = Doc.empty()

    if tyArgs.isEmpty():
        return doc

    doc += Doc.char('[')
    let i: U32 = 0
    for ty: Type in tyArgs.iter():
        if i != 0:
            doc += Doc.str(", ")
        doc += ty.format(tokens)
    doc += Doc.char(']')

    doc


formatNamed(named: Named[a], format: Fn(a, Vec[Token]) Doc / exn, tokens: Vec[Token]) Doc / exn:
    match named.name:
        Option.None:
            format(named.node, tokens)

        Option.Some(name):
            Doc.nested(
                4,
                Doc.str(idText(name, tokens))
                    + Doc.str(" =")
                    + Doc.break_(1)
                    + format(named.node, tokens))
                .group()


idText(id: Id, tokens: Vec[Token]) Str:
    tokens.get(id.token.idx).text


tokenText(token: TokenIdx, tokens: Vec[Token]) Str:
    tokens.get(token.idx).text


join[Iterator[iter, Doc, exn]](iter: iter, sep: Doc) Doc / exn:
    let doc = match iter.next():
        Option.None: return Doc.empty()
        Option.Some(doc): doc

    for d: Doc in iter:
        doc += sep + d

    doc
