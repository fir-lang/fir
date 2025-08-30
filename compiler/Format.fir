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

    # print(tokens)
    # sanityCheckTokens(tokens)

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
    let doc = Doc.empty()
    let declIdx: U32 = 0

    # Print imports (which should come first) without empty lines in between.
    while mod.getOpt(declIdx) is Option.Some(TopDecl.Import(importDecl)):
        if declIdx != 0:
            doc += Doc.hardLine()
        doc += importDecl.format(tokens)
        declIdx += 1

    # Other top-level items get two empty lines in between.
    let emptyLines = Doc.hardLine() + Doc.hardLine() + Doc.hardLine()
    while declIdx < mod.len():
        if declIdx != 0:
            doc += emptyLines
        doc += mod.get(declIdx).format(tokens)
        declIdx += 1

    doc


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
    let type_ = prevNonTrivia(self.name.token, tokens).unwrap()
    assert(tokens.get(type_.idx).kind is TokenKind.Type)

    let doc = formatToken(type_, tokens) + Doc.blank(1) + formatToken(self.name.token, tokens)

    if not self.typeParams.isEmpty():
        let lbracket = prevNonTrivia(self.typeParams.get(0).firstToken(), tokens).unwrap()
        assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

        let lastToken = self.typeParams.last().unwrap().lastToken()

        # Top-level declarations always start at column 0, and I don't think it'll be common to have
        # so many type parameters the parameter list will need line breaks. For now print the header
        # in one line.
        doc += formatToken(lbracket, tokens)

        for typeParam: Id in self.typeParams.iter():
            doc += formatToken(typeParam.token, tokens)
            lastToken = typeParam.token

            if nextNonTrivia(typeParam.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
                doc += formatToken(next, tokens)
                lastToken = next

        let rbracket = nextNonTrivia(lastToken, tokens).unwrap()
        print(tokens.get(lastToken.idx))
        print(tokens.get(rbracket.idx))
        assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

        doc += formatToken(rbracket, tokens)

    if self.rhs is Option.Some(rhs):
        doc += rhs.format(tokens)

    doc


TypeDeclRhs.format(self, tokens: Vec[Token]) Doc:
    match self:
        TypeDeclRhs.Sum(decls):
            let colon = prevNonTrivia(decls.get(0).name.token, tokens).unwrap()
            assert(tokens.get(colon.idx).kind is TokenKind.Colon)

            Doc.nested(4, formatToken(colon, tokens)
                + Doc.hardLine()
                + join(decls.iter().map(|decl: ConDecl|: decl.format(tokens)), Doc.hardLine()))

        TypeDeclRhs.Product(fields):
            fields.format(tokens)


ConDecl.format(self, tokens: Vec[Token]) Doc:
    formatToken(self.name.token, tokens) + self.fields.format(tokens)


ConFields.format(self, tokens: Vec[Token]) Doc:
    match self:
        ConFields.Empty:
            Doc.empty()

        ConFields.Named(fields):
            let lparen = prevNonTrivia(fields.get(0).name.token, tokens).unwrap()
            assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

            let doc = formatToken(lparen, tokens) + Doc.break_(0)

            let lastToken = lparen
            let trailingComma = Bool.False
            for field: (name: Id, ty: Type) in fields.iter():
                let colon = nextNonTrivia(field.name.token, tokens).unwrap()
                assert(tokens.get(colon.idx).kind is TokenKind.Colon)

                doc +=
                    formatToken(field.name.token, tokens)
                        + formatToken(colon, tokens)
                        + field.ty.format(tokens)

                lastToken = field.ty.lastToken()

                if nextNonTrivia(field.ty.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
                    trailingComma = Bool.True
                    doc += formatToken(next, tokens)
                    lastToken = next

            if fields.len() != 0 and not trailingComma:
                doc += Doc.whenNotFlat(Doc.char(','))

            let rparen = nextNonTrivia(lastToken, tokens).unwrap()
            assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

            Doc.grouped(doc.nest(4) + Doc.break_(0) + formatToken(rparen, tokens))

        ConFields.Unnamed(fields):
            let lparen = prevNonTrivia(fields.get(0).firstToken(), tokens).unwrap()
            assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

            let doc = formatToken(lparen, tokens) + Doc.break_(0)

            let lastToken = lparen
            let trailingComma = Bool.False
            for field: Type in fields.iter():
                doc += field.format(tokens)
                lastToken = field.lastToken()

                if nextNonTrivia(lastToken, tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
                    trailingComma = Bool.True
                    doc += formatToken(next, tokens)
                    lastToken = next

            if fields.len() != 0 and not trailingComma:
                doc += Doc.whenNotFlat(Doc.char(','))

            let rparen = nextNonTrivia(lastToken, tokens).unwrap()
            assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

            Doc.grouped(doc.nest(4) + Doc.break_(0) + formatToken(rparen, tokens))


FunDecl.format(self, tokens: Vec[Token]) Doc:
    let doc = match self.parentTy:
        Option.Some(id):
            let dot = nextNonTrivia(id.token, tokens).unwrap()
            assert(tokens.get(dot.idx).kind is TokenKind.Dot)
            formatToken(id.token, tokens) + formatToken(dot, tokens)
        Option.None:
            Doc.empty()

    doc += formatToken(self.name.token, tokens)

    if self.sig.context is Option.Some(context):
        let lbracket = context.firstToken()
        assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

        let rbracket = context.lastToken()
        assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

        doc += formatToken(lbracket, tokens)

        for ty: Type in context.preds.iter():
            doc += ty.format(tokens)
            if nextNonTrivia(ty.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
                doc += formatToken(next, tokens)

        doc += formatToken(rbracket, tokens)

    let lparen = match self.sig.context:
        Option.Some(context): nextNonTrivia(context.lastToken(), tokens).unwrap()
        Option.None: nextNonTrivia(self.name.token, tokens).unwrap()

    assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

    let argList = formatToken(lparen, tokens) + Doc.break_(0)

    let trailingComma = Bool.False
    let lastToken = lparen
    for arg: (name: Id, ty: Option[Type]) in self.sig.params.iter():
        argList += formatToken(arg.name.token, tokens)
        lastToken = arg.name.token

        if arg.ty is Option.Some(ty):
            trailingComma = Bool.False

            let colon = nextNonTrivia(arg.name.token, tokens).unwrap()
            assert(tokens.get(colon.idx).kind is TokenKind.Colon)

            argList += formatToken(colon, tokens) + Doc.blank(1) + ty.format(tokens)
            lastToken = ty.lastToken()

        if nextNonTrivia(lastToken, tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            argList += formatToken(next, tokens) + Doc.blank(1)
            lastToken = next

    if self.sig.params.len() != 0 and not trailingComma:
        argList += Doc.whenNotFlat(Doc.char(','))

    let rparen = nextNonTrivia(lastToken, tokens).unwrap()
    lastToken = rparen
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    argList = argList.nest(4).group() + Doc.break_(0) + formatToken(rparen, tokens)

    doc += argList.group()

    if self.sig.returnTy is Option.Some(ret):
        lastToken = ret.lastToken()
        doc += Doc.blank(1) + ret.format(tokens)

    if self.sig.exceptions is Option.Some(exn):
        let slash = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(slash.idx).kind is TokenKind.Slash)

        doc += Doc.blank(1) + formatToken(slash, tokens) + Doc.blank(1) + exn.format(tokens)
        lastToken = exn.lastToken()

    if self.body is Option.Some(stmts):
        let colon = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(colon.idx).kind is TokenKind.Colon)

        doc += Doc.nested(4, formatToken(colon, tokens) + Doc.hardLine() + formatStmts(stmts, tokens))

    doc


ImportDecl.format(self, tokens: Vec[Token]) Doc:
    let import_ = prevNonTrivia(self.path.get(0).token, tokens).unwrap()
    assert(tokens.get(import_.idx).kind is TokenKind.Import)

    let doc = formatToken(import_, tokens) + Doc.blank(1)

    for id: Id in self.path.iter():
        doc += formatToken(id.token, tokens)

        if nextNonTrivia(id.token, tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Dot:
            doc += formatToken(next, tokens)

    doc


TraitDecl.format(self, tokens: Vec[Token]) Doc:
    let trait_ = prevNonTrivia(self.name.token, tokens).unwrap()
    assert(tokens.get(trait_.idx).kind is TokenKind.Trait)

    let lbracket = prevNonTrivia(self.typeParams.get(0).token, tokens).unwrap()
    assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

    let doc0 = formatToken(trait_, tokens) + Doc.blank(1) + formatToken(self.name.token, tokens)

    let docRest = formatToken(lbracket, tokens)
    let lastToken = lbracket
    for typeParam: Id in self.typeParams.iter():
        lastToken = typeParam.token
        docRest += formatToken(typeParam.token, tokens)
        if nextNonTrivia(typeParam.token, tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            docRest += formatToken(next, tokens)
            lastToken = next

    let rbracket = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

    let colon = nextNonTrivia(rbracket, tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    doc0 + Doc.nested(
        4,
        docRest
            + formatToken(rbracket, tokens)
            + formatToken(colon, tokens)
            + Doc.hardLine()
            + join(self.items.iter().map(|decl: FunDecl|: decl.format(tokens)), Doc.hardLine()))


ImplDecl.format(self, tokens: Vec[Token]) Doc:
    let impl_ = self._firstToken
    let doc0 = formatToken(impl_, tokens)

    let docRest = Doc.empty()

    if self.context is Option.Some(context):
        let lbracket = context.firstToken()
        docRest += formatToken(lbracket, tokens)

        for pred: Type in context.preds.iter():
            docRest += pred.format(tokens)
            if nextNonTrivia(pred.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
                docRest += formatToken(next, tokens)

        let rbracket = context.lastToken()
        docRest += formatToken(rbracket, tokens)

    docRest += Doc.blank(1) + formatToken(self.trait_.token, tokens)

    let lbracket = nextNonTrivia(self.trait_.token, tokens).unwrap()
    assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

    docRest += formatToken(lbracket, tokens)

    let lastToken = lbracket
    for ty: Type in self.tys.iter():
        docRest += ty.format(tokens)
        lastToken = ty.lastToken()
        if nextNonTrivia(ty.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            docRest += formatToken(next, tokens)
            lastToken = next

    let rbracket = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

    let colon = nextNonTrivia(rbracket, tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    docRest += formatToken(rbracket, tokens) + formatToken(colon, tokens) + Doc.hardLine()

    docRest += join(
        self.items.iter().map(|decl: FunDecl|: decl.format(tokens)),
        Doc.hardLine() + Doc.hardLine()
    )

    doc0 + docRest.nest(4)


# --------------------------------------------------------------------------------------------------
# Expressions


Expr.format(self, tokens: Vec[Token]) Doc:
    Doc.group(match self:
        Expr.Var(e): e.format(tokens)
        Expr.ConstrSelect(e): e.format(tokens)
        Expr.FieldSelect(e): e.format(tokens)
        Expr.AssocFnSelect(e): e.format(tokens)
        Expr.Call(e): e.format(tokens)
        Expr.Int(e): e.format(tokens)
        Expr.Str(e): e.format(tokens)
        Expr.Char(e): e.format(tokens)
        Expr.Self(e): formatToken(e, tokens)
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
        Expr.Paren(e): e.format(tokens)

        Expr.MethodSelect(e):
            # These expressions are intoruduced by the type checker, which we don't run when
            # formatting.
            panic("Expr.MethodSelect"))


VarExpr.format(self, tokens: Vec[Token]) Doc:
    formatToken(self.id.token, tokens) + formatTyArgs(self.userTyArgs, tokens)


Constructor.format(self, tokens: Vec[Token]) Doc:
    let doc = formatToken(self.ty.token, tokens)

    if self.constr is Option.Some(con):
        let dot = nextNonTrivia(self.ty.token, tokens).unwrap()
        assert(tokens.get(dot.idx).kind is TokenKind.Dot)

        doc += formatToken(dot, tokens) + formatToken(con.token, tokens)

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
    let fields: Vec[(field: Id, tyArgs: Option[TyArgs])] = Vec.withCapacity(1)
    loop:
        fields.push((field = selection.field, tyArgs = selection.userTyArgs))
        if selection.object is Expr.FieldSelect(e):
            selection = e
        else:
            break

    let doc = selection.object.format(tokens)
    while fields.pop() is Option.Some((field, tyArgs)):
        let dot = prevNonTrivia(field.token, tokens).unwrap()
        assert(tokens.get(dot.idx).kind is TokenKind.Dot)

        doc += Doc.nested(4,
            Doc.break_(0)
                + formatToken(dot, tokens)
                + formatToken(field.token, tokens)
                + formatTyArgs(tyArgs, tokens)).group()

    doc.group()


AssocFnSelectExpr.format(self, tokens: Vec[Token]) Doc:
    let dot = nextNonTrivia(self.ty.token, tokens).unwrap()
    assert(tokens.get(dot.idx).kind is TokenKind.Dot)

    Doc.nested(
        4,
        formatToken(self.ty.token, tokens)
            + Doc.break_(0)
            + formatToken(dot, tokens)
            + formatToken(self.member.token, tokens)
            + formatTyArgs(self.userTyArgs, tokens))


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
    let fun = self.fun.format(tokens)

    let lparen = nextNonTrivia(self.fun.lastToken(), tokens).unwrap()
    assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

    let args = formatToken(lparen, tokens) + Doc.break_(0)
    let trailingComma = Bool.False
    for arg: Named[Expr] in self.args.iter():
        trailingComma = Bool.False
        args += formatNamed(arg, Expr.format, tokens).group()
        if nextNonTrivia(arg.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            args += formatToken(next, tokens) + Doc.break_(1)
            trailingComma = Bool.True

    let rparen = self.lastToken()
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    if self.args.len() != 0 and not trailingComma:
        args += Doc.whenNotFlat(Doc.char(','))

    args = Doc.grouped(args.nest(4) + Doc.break_(0) + formatToken(rparen, tokens))

    Doc.grouped(fun + args)


IntExpr.format(self, tokens: Vec[Token]) Doc:
    formatToken(self.token, tokens)


StrExpr.format(self, tokens: Vec[Token]) Doc:
    formatToken(self.token, tokens)


CharExpr.format(self, tokens: Vec[Token]) Doc:
    formatToken(self.token, tokens)


BinOpExpr.format(self, tokens: Vec[Token]) Doc:
    # Binary operators are all left-associative, so the right-hand side can never be a `BinOp`
    # unless it's wrapped with a `Paren`.
    #
    # Ignore associativities and print the operator before expressions when breaking into lines.

    let rhs = self.right
    let exprs: Vec[(expr: Expr, op: BinOp)] = Vec.withCapacity(1)

    let left = self.left
    while left is Expr.BinOp(binop):
        exprs.push((expr = binop.right, op = binop.op))
        left = binop.left

    let doc0 = left.format(tokens)
    let docRest = Doc.empty()
    while exprs.pop() is Option.Some((expr, op)):
        let opToken = nextNonTrivia(expr.lastToken(), tokens).unwrap()
        docRest += Doc.break_(1) + formatToken(opToken, tokens) + Doc.blank(1) + expr.format(tokens)

    let selfOp = nextNonTrivia(self.left.lastToken(), tokens).unwrap()
    docRest += Doc.break_(1) + formatToken(selfOp, tokens) + Doc.blank(1) + self.right.format(tokens)

    doc0 + docRest.nest(4)


UnOpExpr.format(self, tokens: Vec[Token]) Doc:
    let op = self.firstToken()
    formatToken(op, tokens) + Doc.blank(1) + self.expr.format(tokens)


RecordExpr.format(self, tokens: Vec[Token]) Doc:
    let lparen = self.firstToken()
    assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

    let doc0 = formatToken(lparen, tokens)

    let docRest = Doc.empty()
    let fieldIdx: U32 = 0
    for field: Named[Expr] in self.fields.iter():
        docRest += formatNamed(field, Expr.format, tokens)

        if nextNonTrivia(field.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            docRest += formatToken(next, tokens)

    let rparen = self.lastToken()
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    doc0 + Doc.nested(4, docRest + formatToken(rparen, tokens))


ReturnExpr.format(self, tokens: Vec[Token]) Doc:
    let ret = self.firstToken()
    assert(tokens.get(ret.idx).kind is TokenKind.Return)

    let doc = formatToken(ret, tokens)

    match self.expr:
        Option.None: doc
        Option.Some(expr): doc + Doc.nested(4, Doc.break_(1) + expr.format(tokens))


MatchExpr.format(self, tokens: Vec[Token]) Doc:
    let match_ = self.firstToken()
    assert(tokens.get(match_.idx).kind is TokenKind.Match)

    let colon = nextNonTrivia(self.scrutinee.lastToken(), tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    let doc0 = formatToken(match_, tokens)
    let docRest =
        Doc.nested(8, self.scrutinee.format(tokens))
            + formatToken(colon, tokens)

    for alt: Alt in self.alts.iter():
        docRest += Doc.hardLine() + alt.format(tokens)

    doc0 + docRest.nest(4)


Alt.format(self, tokens: Vec[Token]) Doc:
    let doc0 = self.pattern.format(tokens)
    let docRest = Doc.empty()

    if self.guard is Option.Some(guard):
        let if_ = prevNonTrivia(guard.firstToken(), tokens).unwrap()
        assert(tokens.get(if_.idx).kind is TokenKind.If)

        docRest += Doc.break_(1) + formatToken(if_, tokens) + guard.format(tokens)
        docRest = Doc.nested(8, docRest)

    let body = formatStmts(self.rhs, tokens)

    let colon = prevNonTrivia(self.rhs.get(0).firstToken(), tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    doc0 + Doc.nested(4, docRest + formatToken(colon, tokens) + Doc.break_(1) + body).group()


IfExpr.format(self, tokens: Vec[Token]) Doc:
    let firstBranch = self.branches.get(0)

    let colon = nextNonTrivia(firstBranch.guard.lastToken(), tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    let doc =
        formatToken(self.firstToken(), tokens)
            + Doc.blank(1)
            + Doc.nested(
                4,
                firstBranch.guard.format(tokens)
                + formatToken(colon, tokens)
                + Doc.hardLine()
                + formatStmts(firstBranch.body, tokens))

    for branch: (guard: Expr, body: Vec[Stmt]) in self.branches.iter().skip(1):
        let elif_ = prevNonTrivia(branch.guard.firstToken(), tokens).unwrap()
        assert(tokens.get(elif_.idx).kind is TokenKind.Elif)

        let colon = nextNonTrivia(branch.guard.lastToken(), tokens).unwrap()
        assert(tokens.get(colon.idx).kind is TokenKind.Colon)

        doc += Doc.hardLine()
        doc +=
            formatToken(elif_, tokens)
                + Doc.nested(
                    4,
                    branch.guard.format(tokens)
                        + formatToken(colon, tokens)
                        + Doc.hardLine()
                        + formatStmts(branch.body, tokens))

    if self.elseBranch is Option.Some(body):
        let colon = prevNonTrivia(body.get(0).firstToken(), tokens).unwrap()
        assert(tokens.get(colon.idx).kind is TokenKind.Colon)

        let else_ = prevNonTrivia(colon, tokens).unwrap()
        assert(tokens.get(else_.idx).kind is TokenKind.Else)

        doc += Doc.hardLine()
        doc +=
            formatToken(else_, tokens)
                + Doc.nested(
                    4,
                    formatToken(colon, tokens)
                        + Doc.hardLine()
                        + formatStmts(body, tokens))

    doc


FnExpr.format(self, tokens: Vec[Token]) Doc:
    # assert(self.sig.context.typeParams.isEmpty)
    # assert(self.sig.context.preds.isEmpty)
    # assert(self.sig.self_ is SelfParam.No)

    let pipe1 = self.firstToken()
    let doc0 = formatToken(pipe1, tokens)

    let docRest = Doc.empty()
    let lastToken = pipe1
    for param: (name: Id, ty: Option[Type]) in self.sig.params.iter():
        docRest += formatToken(param.name.token, tokens)
        lastToken = param.name.token

        if param.ty is Option.Some(ty):
            let colon = nextNonTrivia(param.name.token, tokens).unwrap()
            assert(tokens.get(colon.idx).kind is TokenKind.Colon)

            docRest += formatToken(colon, tokens) + ty.format(tokens)
            lastToken = ty.lastToken()

            if nextNonTrivia(ty.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
                docRest += formatToken(next, tokens) + Doc.blank(1)
                lastToken = next

    let pipe2 = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(pipe2.idx).kind is TokenKind.Pipe)

    docRest += formatToken(pipe2, tokens)
    lastToken = pipe2

    if self.sig.returnTy is Option.Some(ret):
        docRest += Doc.blank(1) + ret.format(tokens)
        lastToken = ret.lastToken()

    if self.sig.exceptions is Option.Some(exn):
        docRest += Doc.blank(1) + exn.format(tokens)
        lastToken = exn.lastToken()

    let colon = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    docRest += formatToken(colon, tokens)

    if self.body.len() > 1:
        docRest += Doc.hardLine()
    else:
        docRest += Doc.break_(1)

    docRest += formatStmts(self.body, tokens)

    doc0 + docRest.nest(4)


IsExpr.format(self, tokens: Vec[Token]) Doc:
    let is_ = nextNonTrivia(self.expr.lastToken(), tokens).unwrap()
    assert(tokens.get(is_.idx).kind is TokenKind.Is)

    self.expr.format(tokens)
        + Doc.nested(
            4,
            Doc.break_(1)
                + formatToken(is_, tokens)
                + Doc.blank(1)
                + self.pat.format(tokens))


DoExpr.format(self, tokens: Vec[Token]) Doc:
    let do_ = self.firstToken()

    let colon = nextNonTrivia(do_, tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    formatToken(do_, tokens)
        + Doc.nested(
            4,
            formatToken(colon, tokens)
                + Doc.hardLine() + formatStmts(self.body, tokens))


SeqExpr.format(self, tokens: Vec[Token]) Doc:
    let doc0 = Doc.empty()
    let docRest = Doc.empty()

    if self.ty is Option.Some(ty):
        doc0 += ty.format(tokens)

        let dot = prevNonTrivia(self._lbracket, tokens).unwrap()
        assert(tokens.get(dot.idx).kind is TokenKind.Dot)

        docRest += formatToken(dot, tokens)
        docRest += formatToken(self._lbracket, tokens)
    else:
        doc0 += formatToken(self._lbracket, tokens)

    let trailingComma = Bool.False
    for elem: (key: Option[Expr], value: Expr) in self.elems.iter():
        trailingComma = Bool.False

        if elem.key is Option.Some(key):
            let eq = nextNonTrivia(key.lastToken(), tokens).unwrap()
            assert(tokens.get(eq.idx).kind is TokenKind.Eq)

            docRest += key.format(tokens) + Doc.blank(1) + formatToken(eq, tokens) + Doc.break_(1)

        docRest += elem.value.format(tokens)

        if nextNonTrivia(elem.value.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            docRest += formatToken(next, tokens)

    if self.elems.len() != 0 and not trailingComma:
        docRest += Doc.whenNotFlat(Doc.char(','))

    Doc.grouped(doc0 + docRest.nest(4) + Doc.break_(0) + formatToken(self._rbracket, tokens))


ParenExpr.format(self, tokens: Vec[Token]) Doc:
    formatToken(self.firstToken(), tokens)
        + self.expr.format(tokens)
        + formatToken(self.lastToken(), tokens)


# --------------------------------------------------------------------------------------------------
# Statements


formatStmts(stmts: Vec[Stmt], tokens: Vec[Token]) Doc:
    if stmts.isEmpty():
        Doc.empty()

    let lastStmt = stmts.get(0)
    let doc = lastStmt.format(tokens)

    for stmt: Stmt in stmts.iter().skip(1):
        doc += Doc.hardLine()

        # When we have empty lines between the statements, leave one empty line between the
        # statements.
        if tokens.get(stmt.firstToken().idx).line - tokens.get(lastStmt.lastToken().idx).line > 1:
            doc += Doc.hardLine()

        doc += stmt.format(tokens)

        lastStmt = stmt

    doc


Stmt.format(self, tokens: Vec[Token]) Doc:
    Doc.group(match self:
        Stmt.Let(s): s.format(tokens)
        Stmt.Assign(s): s.format(tokens)
        Stmt.Expr(s): s.format(tokens)
        Stmt.For(s): s.format(tokens)
        Stmt.While(s): s.format(tokens)
        Stmt.Loop(s): s.format(tokens)
        Stmt.Break(s): s.format(tokens)
        Stmt.Continue(s): s.format(tokens))


LetStmt.format(self, tokens: Vec[Token]) Doc:
    let let_ = prevNonTrivia(self.lhs.firstToken(), tokens).unwrap()
    assert(tokens.get(let_.idx).kind is TokenKind.Let)

    let doc = formatToken(let_, tokens) + self.lhs.format(tokens)

    if self.ty is Option.Some(ty):
        let colon = prevNonTrivia(ty.firstToken(), tokens).unwrap()
        assert(tokens.get(colon.idx).kind is TokenKind.Colon)

        doc += formatToken(colon, tokens) + Doc.blank(1) + ty.format(tokens)

    let eq = prevNonTrivia(self.rhs.firstToken(), tokens).unwrap()
    assert(tokens.get(eq.idx).kind is TokenKind.Eq)

    doc + Doc.blank(1) + formatToken(eq, tokens) + Doc.blank(1) + self.rhs.format(tokens)


AssignStmt.format(self, tokens: Vec[Token]) Doc:
    let op = nextNonTrivia(self.lhs.lastToken(), tokens).unwrap()

    self.lhs.format(tokens)
        + Doc.blank(1)
        + formatToken(op, tokens)
        + Doc.blank(1)
        + self.rhs.format(tokens)


ForStmt.format(self, tokens: Vec[Token]) Doc:
    let doc0 = Doc.empty()
    let for_ = self.firstToken()

    if self.label is Option.Some(label):
        doc0 += formatToken(label.token, tokens) + Doc.blank(1)
        for_ = nextNonTrivia(label.token, tokens).unwrap()

    assert(tokens.get(for_.idx).kind is TokenKind.For)

    doc0 += formatToken(for_, tokens) + Doc.blank(1)

    let docRest = self.pat.format(tokens)
    let lastToken = self.pat.lastToken()

    if self.astTy is Option.Some(ty):
        let colon = prevNonTrivia(ty.firstToken(), tokens).unwrap()
        assert(tokens.get(colon.idx).kind is TokenKind.Colon)

        docRest += formatToken(colon, tokens) + Doc.blank(1) + ty.format(tokens) + Doc.blank(1)
        lastToken = ty.lastToken()

    let in_ = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(in_.idx).kind is TokenKind.In)

    let colon = nextNonTrivia(self.expr.lastToken(), tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    docRest += Doc.nested(
        4,
        formatToken(in_, tokens) + Doc.break_(1) + self.expr.format(tokens) + formatToken(colon, tokens))

    doc0 + Doc.nested(4, docRest.group() + Doc.hardLine() + formatStmts(self.body, tokens))


WhileStmt.format(self, tokens: Vec[Token]) Doc:
    let doc0 = Doc.empty()
    let while_ = self.firstToken()

    if self.label is Option.Some(label):
        doc0 += formatToken(label.token, tokens) + Doc.blank(1)
        while_ = nextNonTrivia(label.token, tokens).unwrap()

    assert(tokens.get(while_.idx).kind is TokenKind.While)

    doc0 += formatToken(while_, tokens) + Doc.blank(1)

    let colon = nextNonTrivia(self.cond.lastToken(), tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    doc0 + Doc.nested(4, self.cond.format(tokens).nest(4)
            + formatToken(colon, tokens)
            + Doc.hardLine()
            + formatStmts(self.body, tokens))


LoopStmt.format(self, tokens: Vec[Token]) Doc:
    let loop_ = self.firstToken()

    let colon = nextNonTrivia(loop_, tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    formatToken(loop_, tokens) + Doc.nested(
        4,
        formatToken(colon, tokens)
            + Doc.hardLine()
            + formatStmts(self.body, tokens))


BreakStmt.format(self, tokens: Vec[Token]) Doc:
    let break_ = self.firstToken()

    match self.label:
        Option.None:
            formatToken(break_, tokens)

        Option.Some(label):
            formatToken(break_, tokens) + Doc.nested(4, Doc.break_(1) + formatToken(label.token, tokens))


ContinueStmt.format(self, tokens: Vec[Token]) Doc:
    let continue_ = self.firstToken()

    match self.label:
        Option.None:
            formatToken(continue_, tokens)


        Option.Some(label):
            formatToken(continue_, tokens) + Doc.nested(4, Doc.break_(1) + formatToken(label.token, tokens))


# --------------------------------------------------------------------------------------------------
# Types


Type.format(self, tokens: Vec[Token]) Doc:
    match self:
        Type.Named(t): t.format(tokens)
        Type.Var(id): formatToken(id.token, tokens)
        Type.Record(t): t.format(tokens)
        Type.Variant(t): t.format(tokens)
        Type.Fn_(t): t.format(tokens)


NamedType.format(self, tokens: Vec[Token]) Doc:
    formatToken(self.name.token, tokens) + formatTyArgs(self.args, tokens)


RecordType.format(self, tokens: Vec[Token]) Doc:
    let lparen = self.firstToken()
    assert(tokens.get(lparen.idx).kind is TokenKind.LParen | TokenKind.LParenRow)

    let doc0 = formatToken(lparen, tokens)
    let docRest = Doc.empty()

    let trailingComma = Bool.False
    let lastToken = lparen
    for field: Named[Type] in self.fields.iter():
        trailingComma = Bool.False
        docRest += formatNamed(field, Type.format, tokens)
        lastToken = field.lastToken()
        if nextNonTrivia(field.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            docRest += formatToken(next, tokens)
            trailingComma = Bool.True
            lastToken = next

    if self.extension is Option.Some(ext):
        let dotdot = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)

        docRest += formatToken(dotdot, tokens) + formatToken(ext.token, tokens)

    let rparen = self.lastToken()
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    doc0 + Doc.grouped(docRest + formatToken(rparen, tokens))


VariantType.format(self, tokens: Vec[Token]) Doc:
    let lbracket = self.firstToken()
    assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket | TokenKind.LBracketRow)

    let rbracket = self.lastToken()
    assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

    let doc0 = formatToken(lbracket, tokens)
    let docRest = Doc.empty()

    let trailingComma = Bool.False
    let lastToken = lbracket
    for alt: NamedType in self.alts.iter():
        trailingComma = Bool.False
        docRest += alt.format(tokens)
        if nextNonTrivia(alt.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            docRest += formatToken(next, tokens)
            trailingComma = Bool.True
            lastToken = next

    if self.extension is Option.Some(ext):
        if not self.alts.isEmpty() and not trailingComma:
            docRest += Doc.char(',') + Doc.blank(1)

        let dotdot = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)

        docRest += formatToken(dotdot, tokens) + formatToken(ext.token, tokens)

    doc0 + docRest + formatToken(rbracket, tokens)


FnType.format(self, tokens: Vec[Token]) Doc:
    let fn_ = self.firstToken()

    let lparen = nextNonTrivia(fn_, tokens).unwrap()
    assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

    let doc = formatToken(fn_, tokens) + formatToken(lparen, tokens)

    let lastToken = lparen
    let trailingComma = Bool.False
    for arg: Type in self.args.iter():
        trailingComma = Bool.False
        doc += arg.format(tokens)
        lastToken = arg.lastToken()
        if nextNonTrivia(lastToken, tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            doc += formatToken(next, tokens)
            trailingComma = Bool.True
            lastToken = next

    let rparen = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    doc += formatToken(rparen, tokens)

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
            | Pat.Char(_, p): formatToken(p, tokens)

        Pat.Or(p1, p2):
            # Same formatting as binary operators.
            let pats: Vec[Pat] = Vec.withCapacity(1)

            let left = p1
            while left is Pat.Or(left_, right_):
                pats.push(right_)
                left = left_

            let doc0 = left.format(tokens)
            let docRest = Doc.empty()
            while pats.pop() is Option.Some(pat):
                let pipe = nextNonTrivia(pat.lastToken(), tokens).unwrap()
                assert(tokens.get(pipe.idx).kind is TokenKind.Pipe)

                docRest += Doc.break_(1) + formatToken(pipe, tokens) + Doc.blank(1) + pat.format(tokens)

            let pipe = nextNonTrivia(p1.lastToken(), tokens).unwrap()
            assert(tokens.get(pipe.idx).kind is TokenKind.Pipe)

            docRest += Doc.break_(1) + formatToken(pipe, tokens) + Doc.blank(1) + p2.format(tokens)

            doc0 + docRest.nest(4)


VarPat.format(self, tokens: Vec[Token]) Doc:
    formatToken(self.var_.token, tokens)


ConstrPat.format(self, tokens: Vec[Token]) Doc:
    let con = self.constr.format(tokens)

    if self.fields.isEmpty() and not self.ignoreRest:
        return con

    let lparen = nextNonTrivia(self.constr.lastToken(), tokens).unwrap()
    assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

    let args = formatToken(lparen, tokens) + Doc.break_(0)

    let trailingComma = Bool.False
    let lastToken = lparen
    for field: Named[Pat] in self.fields.iter():
        trailingComma = Bool.False
        args += formatNamed(field, Pat.format, tokens)
        lastToken = field.lastToken()
        if nextNonTrivia(field.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            args += formatToken(next, tokens)
            trailingComma = Bool.True
            lastToken = next

    if self.ignoreRest:
        let dotdot = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)

        args += formatToken(dotdot, tokens)
    elif not trailingComma:
        args += Doc.whenNotFlat(Doc.char(','))

    let rparen = self.lastToken()
    Doc.grouped(con + args.nest(4).group() + Doc.break_(0) + formatToken(rparen, tokens))


RecordPat.format(self, tokens: Vec[Token]) Doc:
    let lparen = self.firstToken()
    let doc = formatToken(lparen, tokens) + Doc.break_(0)

    let trailingComma = Bool.False
    let lastToken = lparen
    for field: Named[Pat] in self.fields.iter():
        trailingComma = Bool.False
        doc += formatNamed(field, Pat.format, tokens)
        lastToken = field.lastToken()
        if nextNonTrivia(field.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
            doc += formatToken(next, tokens)
            trailingComma = Bool.True
            lastToken = next

    if self.ignoreRest:
        let dotdot = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)

        doc += formatToken(dotdot, tokens)
    elif not trailingComma:
        doc += Doc.whenNotFlat(Doc.char(','))

    let rparen = self.lastToken()
    Doc.grouped(doc.nest(4) + Doc.break_(0) + formatToken(rparen, tokens))


# --------------------------------------------------------------------------------------------------


## Format a single token, handling comment tokens that are
##      (1) before the token, that are not with other tokens in their lines.
##      (2) after the token, at the same line with the token being formatted.
formatToken(tokenIdx: TokenIdx, tokens: Vec[Token]) Doc:
    let doc = Doc.empty()

    if findCommentBefore(tokenIdx, tokens) is Option.Some(commentStart):
        let lastCommentToken = tokens.get(commentStart.idx)
        for commentTokenIdx: TokenIdx in range(commentStart, tokenIdx):
            let commentToken = tokens.get(commentTokenIdx.idx)

            if commentToken.kind is TokenKind.Newline | TokenKind.Indent | TokenKind.Dedent:
                continue

            if commentToken.rightLoc().line - lastCommentToken.rightLoc().line > 1:
                doc += Doc.hardLine()

            doc += Doc.str(commentToken.text) + Doc.hardLine()

            lastCommentToken = commentToken

    let token = tokens.get(tokenIdx.idx)
    doc += Doc.str(token.text)

    let tokenLastLine = token.rightLoc().line
    let trailingTokenIdx = tokenIdx.idx + 1
    while tokens.getOpt(trailingTokenIdx) is Option.Some(nextToken):
        if nextToken.kind is TokenKind.Newline | TokenKind.Indent | TokenKind.Dedent:
            trailingTokenIdx += 1
            continue

        if not (nextToken.kind is TokenKind.Comment):
            break

        if nextToken.line != tokenLastLine:
            break

        doc += Doc.blank(1) + Doc.str(nextToken.text)

        let multiLine = nextToken.text.startsWith("#|")
        if multiLine:
            doc += Doc.blank(1)

            # Keep scanning for more multi-line comments.
            trailingTokenIdx += 1
        else:
            doc += Doc.hardLine()

            # Single-line comments end with a newline, so there can't be more comments.
            break

    doc


formatTyArgs(tyArgs: Option[TyArgs], tokens: Vec[Token]) Doc:
    match tyArgs:
        Option.None:
            Doc.empty()

        Option.Some(tyArgs):
            let lbracket = tyArgs.firstToken()
            assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

            let rbracket = tyArgs.lastToken()
            assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

            let doc = formatToken(lbracket, tokens)

            for tyArg: Type in tyArgs.args.iter():
                doc += tyArg.format(tokens)

                if nextNonTrivia(tyArg.lastToken(), tokens) is Option.Some(next) and tokens.get(next.idx).kind is TokenKind.Comma:
                    doc += formatToken(next, tokens)

            doc + formatToken(rbracket, tokens)


formatNamed(named: Named[a], format: Fn(a, Vec[Token]) Doc / exn, tokens: Vec[Token]) Doc / exn:
    match named.name:
        Option.None:
            format(named.node, tokens)

        Option.Some(name):
            let eq = nextNonTrivia(name.token, tokens).unwrap()
            assert(tokens.get(eq.idx).kind is TokenKind.Eq | TokenKind.Colon)

            Doc.nested(
                4,
                formatToken(name.token, tokens)
                    + Doc.blank(1)
                    + formatToken(eq, tokens)
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


# --------------------------------------------------------------------------------------------------


## Find the beginning of comment tokens before `token` that belong to `token`.
findCommentBefore(token: TokenIdx, tokens: Vec[Token]) Option[TokenIdx]:
    let idx = token.idx
    let commentStart: Option[TokenIdx] = Option.None

    while idx != 0:
        let prev = tokens.get(idx - 1)

        if prev.kind is TokenKind.Newline | TokenKind.Dedent | TokenKind.Indent:
            idx -= 1
        elif prev.kind is TokenKind.Comment:
            let prevIdx = TokenIdx(idx = idx - 1)
            if commentAtStart(prevIdx, tokens):
                commentStart = Option.Some(prevIdx)
                idx -= 1
            else:
                break
        else:
            break

    commentStart


## Whether the given token only has trivia tokens before it.
##
## Reminder: trivia is whitespace, indentation, and comments.
commentAtStart(tokenIdx: TokenIdx, tokens: Vec[Token]) Bool:
    let idx = tokenIdx.idx

    if idx == 0:
        return Bool.True

    idx -= 1

    while idx != 0:
        let prev = tokens.get(idx)

        if prev.kind is TokenKind.Comment | TokenKind.Newline | TokenKind.Indent | TokenKind.Dedent:
            idx -= 1
            continue

        break

    if idx == 0 and tokens.get(idx).kind is TokenKind.Comment | TokenKind.Newline | TokenKind.Indent | TokenKind.Dedent:
        return Bool.True

    tokens.get(idx).line != tokens.get(tokenIdx.idx).line


nextNonTrivia(tokenIdx: TokenIdx, tokens: Vec[Token]) Option[TokenIdx]:
    let idx = tokenIdx.idx + 1
    while tokens.getOpt(idx) is Option.Some(next):
        if next.kind is TokenKind.Comment | TokenKind.Newline | TokenKind.Indent | TokenKind.Dedent:
            idx += 1
        else:
            return Option.Some(TokenIdx(idx = idx))

    Option.None


prevNonTrivia(tokenIdx: TokenIdx, tokens: Vec[Token]) Option[TokenIdx]:
    let idx = tokenIdx.idx
    while idx != 0:
        idx -= 1
        let token = tokens.get(idx)
        if not (token.kind is TokenKind.Comment | TokenKind.Newline | TokenKind.Indent | TokenKind.Dedent):
            return Option.Some(TokenIdx(idx = idx))

    Option.None
