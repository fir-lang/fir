import [
    Compiler/Ast,
    Compiler/Error,
    Compiler/Grammar,
    Compiler/Scanner,
]


main():
    let args = getArgs()

    if args.len() != 2:
        showUsageAndExit()

    let path = args.get(1)
    let fileContents = readFileUtf8(path)

    print(formatModuleStr(path, fileContents))


formatModuleStr(moduleName: Str, moduleContents: Str) Str:
    let (tokens, error) = tokenize(moduleName, moduleContents)
    if error is Option.Some(error):
        print("ERROR: `error.loc.line + 1`:`error.loc.col + 1`: `error.msg`")

    # Explicitly close the variant with `row[]` (issue #49).
    let tokens = match try(\(): scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens): tokens.takeArray()

    # print(tokens)
    # sanityCheckTokens(tokens)

    let parserState = ParserState.new(tokens, ())

    let tree = match try(\(): module(parserState)):
        Result.Err(cursor):
            if cursor == tokens.len():
                panic("Parse error: unexpected end of input")
            else:
                panic("Parse error: unexpected token `tokens.get(cursor)`")
        Result.Ok(tree): tree

    formatModule(tree, tokens).render(80).trimAscii()


showUsageAndExit() a:
    panic("USAGE: fir format <file>")


formatModule(mod: Vec[FmtTopDecl], tokens: Array[Token]) Doc:
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

    let eofTokenIdx = TokenIdx(idx = tokens.len())
    if findCommentBefore(eofTokenIdx, tokens) is Option.Some(commentStart):
        if not mod.isEmpty():
            doc += emptyLines
        let comments = formatLeadingComments_(
            commentStart, eofTokenIdx, 2, tokens,
        )
        doc += comments.doc

    doc


# --------------------------------------------------------------------------------------------------
# Declarations


TopDecl.format(self: FmtTopDecl, tokens: Array[Token]) Doc:
    match self:
        TopDecl.Type(d): d.format(tokens)
        TopDecl.Fun(d): d.format(tokens)
        TopDecl.Import(d): d.format(tokens)
        TopDecl.Trait(d): d.format(tokens)
        TopDecl.Impl(d): d.format(tokens)


TypeDecl.format(self: FmtTypeDecl, tokens: Array[Token]) Doc:
    let doc = Doc.empty()

    if self.attr is Option.Some(attr):
        doc += attr.format(tokens) + Doc.hardLine()

    if self.value_ is Option.Some(value_):
        doc += formatToken(value_, tokens) + Doc.blank(1)

    if self.prim_ is Option.Some(prim_):
        doc += formatToken(prim_, tokens) + Doc.blank(1)

    let type_ = prevNonTrivia(self.name.token, tokens).unwrap()
    assert(tokens.get(type_.idx).kind is TokenKind.Type)

    doc += formatToken(type_, tokens)
        + Doc.blank(1)
        + formatToken(self.name.token, tokens)

    if not self.typeParams.isEmpty():
        let lbracket = prevNonTrivia(
            self.typeParams.get(0).firstToken(tokens), tokens,
        ).unwrap()
        assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

        let lastToken = self.typeParams.last().unwrap().lastToken(tokens)

        # Top-level declarations always start at column 0, and I don't think it'll be common to have
        # so many type parameters the parameter list will need line breaks. For now print the header
        # in one line.
        doc += formatToken(lbracket, tokens)

        let trailingComma = Bool.False
        for typeParam: FmtDeclTypeParam in self.typeParams.iter():
            if trailingComma:
                doc += Doc.blank(1)
                trailingComma = Bool.False

            doc += formatToken(typeParam.name.token, tokens)
            lastToken = typeParam.name.token

            if typeParam.kind is Option.Some(kind):
                let colon = nextNonTrivia(typeParam.name.token, tokens).unwrap()
                assert(tokens.get(colon.idx).kind is TokenKind.Colon)
                doc += formatToken(colon, tokens)
                    + Doc.blank(1)
                    + kind.format(tokens)
                lastToken = kind.lastToken(tokens)

            if nextNonTrivia(lastToken, tokens) is Option.Some(next)
                    and tokens.get(next.idx).kind is TokenKind.Comma:
                trailingComma = Bool.True
                doc += formatToken(next, tokens)
                lastToken = next

        let rbracket = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

        doc += formatToken(rbracket, tokens)

    if self.rhs is Option.Some(rhs):
        doc += rhs.format(tokens)

    doc


TypeDeclRhs.format(self: FmtTypeDeclRhs, tokens: Array[Token]) Doc:
    match self:
        TypeDeclRhs.Sum(cons, extension):
            assert(not (cons.isEmpty() and extension is Option.None))

            let colon = match cons.getOpt(0):
                Option.Some(firstCon):
                    prevNonTrivia(firstCon.name.token, tokens).unwrap()
                Option.None:
                    let dotdot = prevNonTrivia(
                        extension.unwrap().firstToken(tokens), tokens,
                    ).unwrap()
                    assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)
                    prevNonTrivia(dotdot, tokens).unwrap()

            assert(tokens.get(colon.idx).kind is TokenKind.Colon)

            let doc = Doc.empty()
            let conIdx: U32 = 0
            for con: FmtConDecl in cons.iter():
                if conIdx != 0:
                    doc += Doc.hardLine()

                    let lastConLastLine = tokens.get(
                        cons.get(conIdx - 1)._lastToken.idx,
                    ).rightLoc().line
                    if tokens.get(con.name.token.idx).line - lastConLastLine > 1:
                        doc += Doc.hardLine()

                doc += con.format(tokens)

                conIdx += 1

            if extension is Option.Some(ext):
                if conIdx != 0:
                    doc += Doc.hardLine()
                let dotdot = prevNonTrivia(ext.firstToken(tokens), tokens)
                    .unwrap()
                assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)
                doc += formatToken(dotdot, tokens) + ext.format(tokens)

            Doc.nested(4, formatToken(colon, tokens) + Doc.hardLine() + doc)

        TypeDeclRhs.Product(fields): fields.format(tokens)

        TypeDeclRhs.Synonym(ty):
            let eq = prevNonTrivia(ty.firstToken(tokens), tokens).unwrap()
            assert(tokens.get(eq.idx).kind is TokenKind.Eq)
            Doc.blank(1)
                + formatToken(eq, tokens)
                + Doc.blank(1)
                + ty.format(tokens)


ConDecl.format(self: FmtConDecl, tokens: Array[Token]) Doc:
    formatToken(self.name.token, tokens) + self.fields.format(tokens)


ConFields.format(self: FmtConFields, tokens: Array[Token]) Doc:
    match self:
        ConFields.Empty: Doc.empty()

        ConFields.Named(fields, extension):
            assert(not (fields.isEmpty() and extension is Option.None))

            let lparen = match fields.getOpt(0):
                Option.Some(firstField):
                    prevNonTrivia(firstField.name.token, tokens).unwrap()
                Option.None:
                    let dotdot = prevNonTrivia(
                        extension.unwrap().firstToken(tokens), tokens,
                    ).unwrap()
                    assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)
                    prevNonTrivia(dotdot, tokens).unwrap()

            assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

            let doc = formatToken(lparen, tokens) + Doc.hardLine()

            let lastToken = lparen
            let trailingComma = Bool.False
            let fieldIdx: U32 = 0
            for field: FmtNamedField in fields.iter():
                if trailingComma:
                    doc += Doc.hardLine()
                    trailingComma = Bool.False

                if fieldIdx != 0:
                    # If there are empty lines between the two fields in the original source then
                    # also leave an empty space between them in the formatted code.
                    let prevFieldLine = tokens.get(lastToken.idx).line
                    let currentFieldLine = tokens.get(field.name.token.idx).line
                    if currentFieldLine - prevFieldLine > 1:
                        doc += Doc.hardLine()

                let colon = nextNonTrivia(field.name.token, tokens).unwrap()
                assert(tokens.get(colon.idx).kind is TokenKind.Colon)

                doc += formatToken(field.name.token, tokens)
                    + formatToken(colon, tokens)
                    + Doc.blank(1)
                    + field.ty.format(tokens)

                lastToken = field.ty.lastToken(tokens)

                if nextNonTrivia(field.ty.lastToken(tokens), tokens)
                        is Option.Some(next)
                        and tokens.get(next.idx).kind is TokenKind.Comma:
                    trailingComma = Bool.True
                    doc += formatToken(next, tokens)
                    lastToken = next

                fieldIdx += 1

            if extension is Option.Some(ext):
                if trailingComma:
                    doc += Doc.hardLine()
                    trailingComma = Bool.False

                # Similar to non-extension fields, allow one empty line between
                # the last field and extension.
                let prevFieldLine = tokens.get(lastToken.idx).line
                let currentFieldLine = tokens.get(ext.firstToken(tokens).idx)
                    .line
                if currentFieldLine - prevFieldLine > 1:
                    doc += Doc.hardLine()

                let dotdot = prevNonTrivia(ext.firstToken(tokens), tokens)
                    .unwrap()
                assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)
                doc += formatToken(dotdot, tokens) + ext.format(tokens)
                lastToken = ext.lastToken(tokens)

            if fields.len() != 0
                    and extension is Option.None
                    and not trailingComma:
                doc += Doc.whenNotFlat(Doc.char(','))

            let rparen = nextNonTrivia(lastToken, tokens).unwrap()
            assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

            doc.nest(4) + Doc.hardLine() + formatToken(rparen, tokens)

        ConFields.Unnamed(fields):
            let lparen = prevNonTrivia(fields.get(0).firstToken(tokens), tokens)
                .unwrap()
            assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

            let doc = formatToken(lparen, tokens) + Doc.break_(0)

            let lastToken = lparen
            let trailingComma = Bool.False
            for field: FmtType in fields.iter():
                if trailingComma:
                    doc += Doc.break_(1)
                    trailingComma = Bool.False

                doc += field.format(tokens)
                lastToken = field.lastToken(tokens)

                if nextNonTrivia(lastToken, tokens) is Option.Some(next)
                        and tokens.get(next.idx).kind is TokenKind.Comma:
                    trailingComma = Bool.True
                    doc += formatToken(next, tokens)
                    lastToken = next

            if fields.len() != 0 and not trailingComma:
                doc += Doc.whenNotFlat(Doc.char(','))

            let rparen = nextNonTrivia(lastToken, tokens).unwrap()
            assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

            Doc.grouped(
                doc.nest(4) + Doc.break_(0) + formatToken(rparen, tokens),
            )


FunDecl.format(self: FmtFunDecl, tokens: Array[Token]) Doc:
    let doc = Doc.empty()

    if self.prim_ is Option.Some(prim_):
        doc += formatToken(prim_, tokens) + Doc.blank(1)

    if self.parentTy is Option.Some(parentTy):
        let dot = nextNonTrivia(parentTy.token, tokens).unwrap()
        assert(tokens.get(dot.idx).kind is TokenKind.Dot)
        doc += formatToken(parentTy.token, tokens) + formatToken(dot, tokens)

    doc += formatToken(self.name.token, tokens)

    doc += _formatOptContext(self.sig.context, tokens)

    let lparen = match self.sig.context:
        Option.Some(context):
            nextNonTrivia(context.lastToken(tokens), tokens).unwrap()
        Option.None: nextNonTrivia(self.name.token, tokens).unwrap()

    assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

    let argListRet = _formatSigArgList(lparen, self.sig.params, tokens)
    let argList = argListRet.doc
    let rparen = argListRet.rparen

    let lastToken = rparen

    argList = argList.nest(4) + Doc.break_(0) + formatToken(rparen, tokens)

    doc += argList.group()

    if self.sig.returnTy is Option.Some(ret):
        lastToken = ret.lastToken(tokens)
        doc += Doc.blank(1) + ret.format(tokens)

    if self.sig.exceptions is Option.Some(exn):
        let slash = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(slash.idx).kind is TokenKind.Slash)

        doc += Doc.blank(1)
            + formatToken(slash, tokens)
            + Doc.blank(1)
            + exn.format(tokens)
        lastToken = exn.lastToken(tokens)

    if self.body is Option.Some(stmts):
        let colon = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(colon.idx).kind is TokenKind.Colon)

        doc += Doc.nested(
            4,
            formatToken(colon, tokens)
                + Doc.hardLine()
                + formatStmts(stmts, tokens),
        )

    doc


_formatOptContext(context: Option[FmtContext], tokens: Array[Token]) Doc:
    match context:
        Option.None: Doc.empty()
        Option.Some(context): _formatContext(context, tokens)


_formatContext(context: FmtContext, tokens: Array[Token]) Doc:
    let lbracket = context.firstToken(tokens)
    assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

    let rbracket = context.lastToken(tokens)
    assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

    let doc = formatToken(lbracket, tokens) + Doc.break_(0)

    let lastToken = lbracket
    let trailingComma = Bool.False
    for pred: FmtPred_ in context.preds.iter():
        if trailingComma:
            doc += Doc.break_(1)
            trailingComma = Bool.False

        match pred:
            Pred_.Kind(name = kindVar, kind):
                doc += formatToken(kindVar.token, tokens)
                lastToken = kindVar.token
                if kind is Option.Some(kind):
                    let colon = nextNonTrivia(kindVar.token, tokens).unwrap()
                    assert(tokens.get(colon.idx).kind is TokenKind.Colon)
                    doc += formatToken(colon, tokens)
                        + Doc.blank(1)
                        + kind.format(tokens)
                    lastToken = kind.lastToken(tokens)
            Pred_.App(app):
                doc += app.format(tokens)
                lastToken = app.lastToken(tokens)
            Pred_.AssocTyEq(ty, assocTy, eq):
                doc += ty.format(tokens)

                let dot = nextNonTrivia(ty.lastToken(tokens), tokens).unwrap()
                assert(tokens.get(dot.idx).kind is TokenKind.Dot)
                doc += formatToken(dot, tokens)
                doc += formatToken(assocTy.token, tokens)

                let eqToken = nextNonTrivia(assocTy.token, tokens).unwrap()
                assert(tokens.get(eqToken.idx).kind is TokenKind.Eq)
                doc += Doc.blank(1)
                    + formatToken(eqToken, tokens)
                    + Doc.blank(1)
                doc += eq.format(tokens)
                lastToken = eq.lastToken(tokens)

        if nextNonTrivia(lastToken, tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            doc += formatToken(next, tokens)

    if context.preds.len() != 0 and not trailingComma:
        doc += Doc.whenNotFlat(Doc.char(','))

    Doc.grouped(doc.nest(4) + Doc.break_(0) + formatToken(rbracket, tokens))


_formatSigArgList(
    lparen: TokenIdx,
    params: Vec[FmtFunArg],
    tokens: Array[Token],
) (doc: Doc, rparen: TokenIdx):
    let argList = formatToken(lparen, tokens) + Doc.break_(0)

    let trailingComma = Bool.False
    let lastToken = lparen
    for arg: FmtFunArg in params.iter():
        if trailingComma:
            argList += Doc.break_(1)
            trailingComma = Bool.False

        argList += formatToken(arg.name.token, tokens)
        lastToken = arg.name.token

        if arg.ty is Option.Some(ty):
            let colon = nextNonTrivia(arg.name.token, tokens).unwrap()
            assert(tokens.get(colon.idx).kind is TokenKind.Colon)

            argList += formatToken(colon, tokens)
                + Doc.blank(1)
                + ty.format(tokens)
            lastToken = ty.lastToken(tokens)

        if nextNonTrivia(lastToken, tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            argList += formatToken(next, tokens)
            lastToken = next

    if params.len() != 0 and not trailingComma:
        argList += Doc.whenNotFlat(Doc.char(','))

    let rparen = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    (doc = argList, rparen = rparen)


ImportDecl.format(self, tokens: Array[Token]) Doc:
    assert(not self.items.isEmpty())

    let firstItemFirstToken = self.items.get(0).path.get(0).token
    let lbracket = prevNonTrivia(firstItemFirstToken, tokens).unwrap()
    assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

    let import_ = prevNonTrivia(lbracket, tokens).unwrap()
    assert(tokens.get(import_.idx).kind is TokenKind.Import)

    # Leading comments of `import` contain hard line breaks; keep them outside
    # the group so they don't force the group to break.
    let leading = formatLeadingComments(import_, tokens)
    let header = Doc.str(tokens.get(import_.idx).text)
        + formatTrailingComments(import_, tokens)
        + Doc.blank(1)
        + formatToken(lbracket, tokens)

    # Single-item imports stay on one line if they fit (using `break_(0)` so the
    # group can still break when the item is too long). Multi-item imports are
    # forced to break with `hardLine`.
    let docRest = if self.items.len() == 1:
        Doc.break_(0)
    else:
        Doc.hardLine()

    let lastToken = lbracket

    let itemIdx: U32 = 0
    let trailingComma = Bool.False
    for item: ImportItem in self.items.iter():
        let itemRet = item.format(tokens)
        docRest += itemRet.doc
        lastToken = itemRet.lastToken

        if nextNonTrivia(lastToken, tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            lastToken = next
            docRest += formatToken(next, tokens)

        if itemIdx == self.items.len() - 1:
            if self.items.len() > 1 and not trailingComma:
                docRest += Doc.whenNotFlat(Doc.char(','))
        else:
            docRest += Doc.hardLine()

        trailingComma = Bool.False

        itemIdx += 1

    let rbracket = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

    if self.items.len() == 1:
        leading
            + Doc.grouped(
                header
                    + docRest.nest(4)
                    + Doc.break_(0)
                    + formatToken(rbracket, tokens),
            )
    else:
        leading
            + header
            + docRest.nest(4)
            + Doc.hardLine()
            + formatToken(rbracket, tokens)


ImportItem.format(self, tokens: Array[Token]) (doc: Doc, lastToken: TokenIdx):
    let doc = Doc.empty()
    let lastToken = self.path.get(0).token

    # Format the path tokens (`A/B/C`). For wildcard and selective specs the
    # path is followed by a `/` which is consumed here as the trailing slash
    # of the last `UpperId`.
    for id: Id in self.path.iter():
        lastToken = id.token
        doc += formatToken(id.token, tokens)
        if nextNonTrivia(id.token, tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Slash:
            lastToken = next
            doc += formatToken(next, tokens)

    match self.importSpec:
        ImportSpec.Wildcard:
            let star = nextNonTrivia(lastToken, tokens).unwrap()
            assert(tokens.get(star.idx).kind is TokenKind.Star)
            doc += formatToken(star, tokens)
            lastToken = star

        ImportSpec.Prefixed(prefix):
            # When the prefix is the default (last segment of the path) the
            # parser stores the same token, so there's no `as` clause to print.
            let lastPathToken = self.path.last().unwrap().token
            if prefix.token.idx != lastPathToken.idx:
                let asKw = nextNonTrivia(lastToken, tokens).unwrap()
                assert(tokens.get(asKw.idx).kind is TokenKind.As)
                doc += Doc.blank(1)
                    + formatToken(asKw, tokens)
                    + Doc.blank(1)
                    + formatToken(prefix.token, tokens)
                lastToken = prefix.token

        ImportSpec.Selective(names):
            let lbracket = nextNonTrivia(lastToken, tokens).unwrap()
            assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

            let listDoc = formatToken(lbracket, tokens) + Doc.break_(0)
            let listLastToken = lbracket
            let listTrailingComma = Bool.False

            for name: ImportName in names.iter():
                if listTrailingComma:
                    listDoc += Doc.break_(1)
                    listTrailingComma = Bool.False

                listDoc += formatToken(name.originalName.token, tokens)
                listLastToken = name.originalName.token

                if name.originalName.token.idx != name.localName.token.idx:
                    let asKw = nextNonTrivia(listLastToken, tokens).unwrap()
                    assert(tokens.get(asKw.idx).kind is TokenKind.As)
                    listDoc += Doc.blank(1)
                        + formatToken(asKw, tokens)
                        + Doc.blank(1)
                        + formatToken(name.localName.token, tokens)
                    listLastToken = name.localName.token

                if nextNonTrivia(listLastToken, tokens) is Option.Some(next)
                        and tokens.get(next.idx).kind is TokenKind.Comma:
                    listTrailingComma = Bool.True
                    listDoc += formatToken(next, tokens)
                    listLastToken = next

            if not names.isEmpty() and not listTrailingComma:
                listDoc += Doc.whenNotFlat(Doc.char(','))

            let rbracket = nextNonTrivia(listLastToken, tokens).unwrap()
            assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

            doc += Doc.grouped(
                listDoc.nest(4) + Doc.break_(0) + formatToken(rbracket, tokens),
            )
            lastToken = rbracket

    (doc = doc, lastToken = lastToken)


TraitDecl.format(self: FmtTraitDecl, tokens: Array[Token]) Doc:
    let trait_ = prevNonTrivia(self.name.token, tokens).unwrap()
    assert(tokens.get(trait_.idx).kind is TokenKind.Trait)

    let lbracket = prevNonTrivia(self.typeParams.get(0).name.token, tokens)
        .unwrap()
    assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

    let doc0 = formatToken(trait_, tokens)
        + Doc.blank(1)
        + formatToken(self.name.token, tokens)

    let docRest = formatToken(lbracket, tokens)
    let lastToken = lbracket
    let trailingComma = Bool.False
    for typeParam: FmtDeclTypeParam in self.typeParams.iter():
        if trailingComma:
            docRest += Doc.blank(1)
            trailingComma = Bool.False

        lastToken = typeParam.name.token
        docRest += formatToken(typeParam.name.token, tokens)

        if typeParam.kind is Option.Some(kind):
            let colon = nextNonTrivia(typeParam.name.token, tokens).unwrap()
            assert(tokens.get(colon.idx).kind is TokenKind.Colon)
            docRest += formatToken(colon, tokens)
                + Doc.blank(1)
                + kind.format(tokens)
            lastToken = kind.lastToken(tokens)

        if nextNonTrivia(lastToken, tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            docRest += formatToken(next, tokens)
            lastToken = next

    let rbracket = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

    docRest += formatToken(rbracket, tokens)

    if self.items.isEmpty():
        return doc0 + docRest

    let colon = nextNonTrivia(rbracket, tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    doc0
        + Doc.nested(
            4,
            docRest
                + formatToken(colon, tokens)
                + Doc.hardLine()
                + join(
                    self.items.iter().map(
                        \(item: FmtTraitDeclItem): item.format(tokens),
                    ),
                    Doc.hardLine() + Doc.hardLine(),
                ),
        )


TraitDeclItem.format(self: FmtTraitDeclItem, tokens: Array[Token]) Doc:
    match self:
        TraitDeclItem.Type(name, kind, default):
            let typeToken = prevNonTrivia(name.token, tokens).unwrap()
            assert(tokens.get(typeToken.idx).kind is TokenKind.Type)

            let doc = formatToken(typeToken, tokens)
                + Doc.blank(1)
                + formatToken(name.token, tokens)

            if kind is Option.Some(kind):
                let colon = nextNonTrivia(name.token, tokens).unwrap()
                assert(tokens.get(colon.idx).kind is TokenKind.Colon)
                doc += formatToken(colon, tokens)
                    + Doc.blank(1)
                    + kind.format(tokens)

            if default is Option.Some(default):
                let eq = prevNonTrivia(default.firstToken(tokens), tokens)
                    .unwrap()
                assert(tokens.get(eq.idx).kind is TokenKind.Eq)
                doc += Doc.blank(1)
                    + formatToken(eq, tokens)
                    + Doc.blank(1)
                    + default.format(tokens)

            doc

        TraitDeclItem.Fun(fun): fun.format(tokens)


ImplDecl.format(self: FmtImplDecl, tokens: Array[Token]) Doc:
    let impl_ = self._firstToken
    assert(tokens.get(impl_.idx).kind is TokenKind.Impl)

    let doc0 = formatToken(impl_, tokens)
        + _formatOptContext(self.context, tokens)

    let docRest = Doc.blank(1) + formatToken(self.trait_.token, tokens)

    let lbracket = nextNonTrivia(self.trait_.token, tokens).unwrap()
    assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

    docRest += formatToken(lbracket, tokens)

    let lastToken = lbracket
    let trailingComma = Bool.False
    for ty: FmtType in self.tys.iter():
        if trailingComma:
            docRest += Doc.blank(1)
            trailingComma = Bool.False

        docRest += ty.format(tokens)
        lastToken = ty.lastToken(tokens)

        if nextNonTrivia(ty.lastToken(tokens), tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            docRest += formatToken(next, tokens)
            lastToken = next

    let rbracket = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

    docRest += formatToken(rbracket, tokens)

    if self.items.isEmpty():
        return doc0 + docRest

    let colon = nextNonTrivia(rbracket, tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    docRest += formatToken(colon, tokens) + Doc.hardLine()

    docRest += join(
        self.items.iter().map(\(item: FmtImplDeclItem): item.format(tokens)),
        Doc.hardLine() + Doc.hardLine(),
    )

    doc0 + docRest.nest(4)


ImplDeclItem.format(self: FmtImplDeclItem, tokens: Array[Token]) Doc:
    match self:
        ImplDeclItem.Type(assocTy, rhs):
            let typeToken = prevNonTrivia(assocTy.token, tokens).unwrap()
            assert(tokens.get(typeToken.idx).kind is TokenKind.Type)

            let eqToken = nextNonTrivia(assocTy.token, tokens).unwrap()
            assert(tokens.get(eqToken.idx).kind is TokenKind.Eq)

            formatToken(typeToken, tokens)
                + Doc.blank(1)
                + formatToken(assocTy.token, tokens)
                + Doc.blank(1)
                + formatToken(eqToken, tokens)
                + Doc.blank(1)
                + rhs.format(tokens)

        ImplDeclItem.Fun(fun): fun.format(tokens)


# --------------------------------------------------------------------------------------------------
# Expressions


Expr.format(self: FmtExpr, tokens: Array[Token]) Doc:
    Doc.group(
        match self:
            Expr.Var(e): e.format(tokens)
            Expr.ConSel(e): e.format(tokens)
            Expr.FieldSel(e): e.format(tokens)
            Expr.AssocFnSel(e): e.format(tokens)
            Expr.Call(e): e.format(tokens)
            Expr.Int(e): e.format(tokens)
            Expr.Str(e): e.format(tokens)
            Expr.Char(e): e.format(tokens)
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
            Expr.Variant(e): e.format(tokens),
    )


VarExpr.format(self: FmtVarExpr, tokens: Array[Token]) Doc:
    formatToken(self.id.token, tokens) + formatTyArgs(self.userTyArgs, tokens)


Con.format(self: FmtCon, tokens: Array[Token]) Doc:
    let doc = formatToken(self.ty.token, tokens)

    if self.con is Option.Some(con):
        let dot = nextNonTrivia(self.ty.token, tokens).unwrap()
        assert(tokens.get(dot.idx).kind is TokenKind.Dot)

        doc += formatToken(dot, tokens) + formatToken(con.token, tokens)

    doc + formatTyArgs(self.userTyArgs, tokens)


FieldSelExpr.format(self: FmtFieldSelExpr, tokens: Array[Token]) Doc:
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
    let fields: Vec[(field: Id, tyArgs: Option[FmtTyArgs])] = Vec.withCapacity(
        1
    )
    loop:
        fields.push((field = selection.field, tyArgs = selection.userTyArgs))
        if selection.object is Expr.FieldSel(e):
            selection = e
        else:
            break

    let doc = selection.object.format(tokens)
    while fields.pop() is Option.Some((field, tyArgs)):
        let dot = prevNonTrivia(field.token, tokens).unwrap()
        assert(tokens.get(dot.idx).kind is TokenKind.Dot)

        doc += Doc.nested(
            4,
            Doc.break_(0)
                + formatToken(dot, tokens)
                + formatToken(field.token, tokens)
                + formatTyArgs(tyArgs, tokens),
        ).group()

    doc.group()


AssocFnSelExpr.format(self: FmtAssocFnSelExpr, tokens: Array[Token]) Doc:
    let dot = nextNonTrivia(self.ty.token, tokens).unwrap()
    assert(tokens.get(dot.idx).kind is TokenKind.Dot)

    Doc.nested(
        4,
        formatToken(self.ty.token, tokens)
            + Doc.break_(0)
            + formatToken(dot, tokens)
            + formatToken(self.member.token, tokens)
            + formatTyArgs(self.userTyArgs, tokens),
    )


CallExpr.format(self: FmtCallExpr, tokens: Array[Token]) Doc:
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

    let lparen = nextNonTrivia(self.fun.lastToken(tokens), tokens).unwrap()
    assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

    let rparen = self.lastToken(tokens)
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    Doc.grouped(
        fun + _formatArgList(self.args, self.splice, lparen, rparen, tokens)
    )


IntExpr.format(self, tokens: Array[Token]) Doc:
    formatToken(self.token, tokens)


StrExpr.format(self: FmtStrExpr, tokens: Array[Token]) Doc:
    let doc = formatToken(self.first, tokens)
    for part: FmtStrPart in self.parts.iter():
        match part:
            StrPart.Str(str): doc += Doc.str(str)
            StrPart.Expr(expr):
                doc += Doc.char('`') + expr.format(tokens) + Doc.char('`')
    doc + formatToken(self.last, tokens)


CharExpr.format(self, tokens: Array[Token]) Doc:
    formatToken(self.token, tokens)


BinOpExpr.format(self: FmtBinOpExpr, tokens: Array[Token]) Doc:
    # Binary operators are all left-associative, so the right-hand side can never be a `BinOp`
    # unless it's wrapped with a `Paren`.
    #
    # Ignore associativities and print the operator before expressions when breaking into lines.

    let rhs = self.right

    let exprs: Vec[FmtExpr] = Vec.withCapacity(1)

    let left = self.left
    while left is Expr.BinOp(binop) and binop.op == self.op:
        exprs.push(binop.right)
        left = binop.left
    exprs.push(left)

    # Leftmost expr
    let expr0 = exprs.pop().unwrap()

    let doc0 = expr0.format(tokens)
    let op0 = nextNonTrivia(expr0.lastToken(tokens), tokens).unwrap()
    let docRest = Doc.break_(1) + formatToken(op0, tokens)

    while exprs.pop() is Option.Some(expr):
        let opToken = nextNonTrivia(expr.lastToken(tokens), tokens).unwrap()
        docRest += Doc.blank(1)
            + expr.format(tokens)
            + Doc.break_(1)
            + formatToken(opToken, tokens)

    let rhsOp = prevNonTrivia(rhs.firstToken(tokens), tokens).unwrap()
    docRest += Doc.blank(1) + rhs.format(tokens)

    Doc.grouped(doc0.group() + docRest.nest(4).group())


UnOpExpr.format(self: FmtUnOpExpr, tokens: Array[Token]) Doc:
    let op = self.firstToken(tokens)
    formatToken(op, tokens) + Doc.blank(1) + self.expr.format(tokens)


RecordExpr.format(self: FmtRecordExpr, tokens: Array[Token]) Doc:
    let lparen = self.firstToken(tokens)
    assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

    let rparen = self.lastToken(tokens)
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    _formatArgList(self.fields, self.splice, lparen, rparen, tokens)


_formatArgList(
    args: Vec[Named[FmtExpr]],
    splice: Option[FmtExpr],
    lparen: TokenIdx,
    rparen: TokenIdx,
    tokens: Array[Token],
) Doc:
    if args.isEmpty() and splice is Option.None:
        return formatToken(lparen, tokens) + formatToken(rparen, tokens)

    let doc = Doc.empty()
    let fieldIdx: U32 = 0
    let trailingComma = Bool.False

    for arg: Named[FmtExpr] in args.iter():
        if trailingComma:
            doc += Doc.break_(1)
            trailingComma = Bool.False

        doc += formatNamed(arg, Expr.format, tokens)

        if nextNonTrivia(arg.lastToken(tokens), tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            doc += formatToken(next, tokens)

    if splice is Option.Some(splice):
        let dotdot = prevNonTrivia(splice.firstToken(tokens), tokens).unwrap()
        assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)
        if args.len() != 0:
            doc += Doc.break_(1)
        doc += formatToken(dotdot, tokens) + splice.format(tokens)

    if args.len() != 0 and splice is Option.None and not trailingComma:
        doc += Doc.whenNotFlat(Doc.char(','))

    formatToken(lparen, tokens)
        + Doc.grouped(
            Doc.nested(4, Doc.break_(0) + doc.group())
                + Doc.break_(0)
                + formatToken(rparen, tokens),
        )


ReturnExpr.format(self: FmtReturnExpr, tokens: Array[Token]) Doc:
    let ret = self.firstToken(tokens)
    assert(tokens.get(ret.idx).kind is TokenKind.Return)

    let doc = formatToken(ret, tokens)

    match self.expr:
        Option.None: doc
        Option.Some(expr):
            # Note: in some cases we may want the `blank` below to be a `break`, e.g. maybe when the
            # expression is a binary operation.
            doc + Doc.blank(1) + expr.format(tokens)


MatchExpr.format(self: FmtMatchExpr, tokens: Array[Token]) Doc:
    let match_ = self.firstToken(tokens)
    assert(tokens.get(match_.idx).kind is TokenKind.Match)

    let colon = nextNonTrivia(self.scrutinee.lastToken(tokens), tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    let doc0 = formatToken(match_, tokens) + Doc.blank(1)
    let docRest = Doc.nested(8, self.scrutinee.format(tokens))
        + formatToken(colon, tokens)

    let altIdx: U32 = 0
    for alt: FmtAlt in self.alts.iter():
        docRest += Doc.hardLine() + alt.format(tokens)

        if self.alts.getOpt(altIdx + 1) is Option.Some(nextAlt):
            if tokens.get(nextAlt.firstToken(tokens).idx).line
                    - tokens.get(alt.lastToken(tokens).idx).rightLoc().line > 1:
                docRest += Doc.hardLine()

        altIdx += 1

    doc0 + docRest.nest(4)


Alt.format(self: FmtAlt, tokens: Array[Token]) Doc:
    let doc0 = self.pat.format(tokens)
    let docRest = Doc.empty()

    if self.guard is Option.Some(guard):
        let if_ = prevNonTrivia(guard.firstToken(tokens), tokens).unwrap()
        assert(tokens.get(if_.idx).kind is TokenKind.If)

        docRest += Doc.break_(1)
            + formatToken(if_, tokens)
            + Doc.blank(1)
            + guard.format(tokens)
        docRest = Doc.nested(4, docRest).group()

    let body = formatStmts(self.rhs, tokens)

    let colon = prevNonTrivia(self.rhs.get(0).firstToken(tokens), tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    doc0
        + Doc.nested(
            4, docRest + formatToken(colon, tokens) + Doc.break_(1) + body,
        ).group()


IfExpr.format(self: FmtIfExpr, tokens: Array[Token]) Doc:
    let firstBranch = self.branches.get(0)

    let colon = nextNonTrivia(firstBranch.guard.lastToken(tokens), tokens)
        .unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    let doc = formatToken(self.firstToken(tokens), tokens)
        + Doc.blank(1)
        + Doc.nested(
            4,
            firstBranch.guard.format(tokens)
                + formatToken(colon, tokens)
                + Doc.hardLine()
                + formatStmts(firstBranch.body, tokens),
        )

    for branch: FmtIfBranch in self.branches.iter().skip(1):
        let elif_ = prevNonTrivia(branch.guard.firstToken(tokens), tokens)
            .unwrap()
        assert(tokens.get(elif_.idx).kind is TokenKind.Elif)

        let colon = nextNonTrivia(branch.guard.lastToken(tokens), tokens).unwrap()
        assert(tokens.get(colon.idx).kind is TokenKind.Colon)

        doc += Doc.hardLine()
        doc += formatToken(elif_, tokens)
            + Doc.blank(1)
            + Doc.nested(
                4,
                branch.guard.format(tokens)
                    + formatToken(colon, tokens)
                    + Doc.hardLine()
                    + formatStmts(branch.body, tokens),
            )

    if self.elseBranch is Option.Some(body):
        let colon = prevNonTrivia(body.get(0).firstToken(tokens), tokens).unwrap()
        assert(tokens.get(colon.idx).kind is TokenKind.Colon)

        let else_ = prevNonTrivia(colon, tokens).unwrap()
        assert(tokens.get(else_.idx).kind is TokenKind.Else)

        doc += Doc.hardLine()
        doc += formatToken(else_, tokens)
            + Doc.nested(
                4,
                formatToken(colon, tokens)
                    + Doc.hardLine()
                    + formatStmts(body, tokens),
            )

    doc


FnExpr.format(self: FmtFnExpr, tokens: Array[Token]) Doc:
    # assert(self.sig.context.typeParams.isEmpty)
    # assert(self.sig.context.preds.isEmpty)
    # assert(self.sig.self_ is SelfParam.No)

    let lparen = self.firstToken(tokens)
    assert(tokens.get(lparen.idx).kind is TokenKind.BackslashLParen)

    let doc0 = formatToken(lparen, tokens)

    let docRest = Doc.empty()
    let lastToken = lparen

    let trailingComma = Bool.False
    for param: FmtFunArg in self.sig.params.iter():
        if trailingComma:
            docRest += Doc.blank(1)
            trailingComma = Bool.False

        docRest += formatToken(param.name.token, tokens)
        lastToken = param.name.token

        if param.ty is Option.Some(ty):
            let colon = nextNonTrivia(param.name.token, tokens).unwrap()
            assert(tokens.get(colon.idx).kind is TokenKind.Colon)

            docRest += formatToken(colon, tokens)
                + Doc.blank(1)
                + ty.format(tokens)
            lastToken = ty.lastToken(tokens)

            if nextNonTrivia(ty.lastToken(tokens), tokens) is Option.Some(next)
                    and tokens.get(next.idx).kind is TokenKind.Comma:
                trailingComma = Bool.True
                docRest += formatToken(next, tokens)
                lastToken = next

    let rparen = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    docRest += formatToken(rparen, tokens)
    lastToken = rparen

    if self.sig.returnTy is Option.Some(ret):
        docRest += Doc.blank(1) + ret.format(tokens)
        lastToken = ret.lastToken(tokens)

    if self.sig.exceptions is Option.Some(exn):
        let slash = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(slash.idx).kind is TokenKind.Slash)

        docRest += Doc.blank(1)
            + formatToken(slash, tokens)
            + Doc.blank(1)
            + exn.format(tokens)
        lastToken = exn.lastToken(tokens)

    let colon = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    docRest += formatToken(colon, tokens)

    if self.body.len() > 1:
        docRest += Doc.hardLine()
    else:
        docRest += Doc.break_(1)

    docRest += formatStmts(self.body, tokens)

    doc0 + docRest.nest(4)


IsExpr.format(self: FmtIsExpr, tokens: Array[Token]) Doc:
    let is_ = nextNonTrivia(self.expr.lastToken(tokens), tokens).unwrap()
    assert(tokens.get(is_.idx).kind is TokenKind.Is)

    Doc.grouped(
        self.expr.format(tokens)
            + Doc.nested(
                4,
                Doc.break_(1)
                    + formatToken(is_, tokens)
                    + Doc.blank(1)
                    + self.pat.format(tokens),
            ),
    )


DoExpr.format(self: FmtDoExpr, tokens: Array[Token]) Doc:
    let do_ = self.firstToken(tokens)

    let colon = nextNonTrivia(do_, tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    formatToken(do_, tokens)
        + Doc.nested(
            4,
            formatToken(colon, tokens)
                + Doc.hardLine()
                + formatStmts(self.body, tokens),
        )


SeqExpr.format(self: FmtSeqExpr, tokens: Array[Token]) Doc:
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

    if self.elems.isEmpty():
        return doc0 + docRest + formatToken(self._rbracket, tokens)

    docRest += Doc.break_(0)

    let trailingComma = Bool.False
    for elem: FmtSeqElem in self.elems.iter():
        if trailingComma:
            docRest += Doc.break_(1)
            trailingComma = Bool.False

        docRest += match elem.key:
            Option.None: elem.val.format(tokens)
            Option.Some(key):
                let eq = nextNonTrivia(key.lastToken(tokens), tokens).unwrap()
                assert(tokens.get(eq.idx).kind is TokenKind.Eq)

                Doc.grouped(
                    key.format(tokens)
                        + Doc.blank(1)
                        + formatToken(eq, tokens)
                        + Doc.break_(1)
                        + elem.val.format(tokens),
                )

        if nextNonTrivia(elem.val.lastToken(tokens), tokens)
                is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            docRest += formatToken(next, tokens)

    if self.elems.len() != 0 and not trailingComma:
        docRest += Doc.whenNotFlat(Doc.char(','))

    Doc.grouped(
        doc0
            + Doc.grouped(docRest.nest(4) + Doc.break_(0))
            + formatToken(self._rbracket, tokens),
    )


ParenExpr.format(self: FmtParenExpr, tokens: Array[Token]) Doc:
    formatToken(self.firstToken(tokens), tokens)
        + self.expr.format(tokens)
        + formatToken(self.lastToken(tokens), tokens)


VariantExpr.format(self: FmtVariantExpr, tokens: Array[Token]) Doc:
    formatToken(self.firstToken(tokens), tokens) + self.expr.format(tokens)


# --------------------------------------------------------------------------------------------------
# Statements


formatStmts(stmts: Vec[FmtStmt], tokens: Array[Token]) Doc:
    if stmts.isEmpty():
        Doc.empty()

    let lastStmt = stmts.get(0)
    let doc = lastStmt.format(tokens)

    for stmt: FmtStmt in stmts.iter().skip(1):
        doc += Doc.hardLine()

        # When we have empty lines between the statements, leave one empty line between the
        # statements.
        if tokens.get(stmt.firstToken(tokens).idx).line
                - tokens.get(lastStmt.lastToken(tokens).idx).line > 1:
            doc += Doc.hardLine()

        doc += stmt.format(tokens)

        lastStmt = stmt

    doc


Stmt.format(self: FmtStmt, tokens: Array[Token]) Doc:
    Doc.group(
        match self:
            Stmt.Let(s): s.format(tokens)
            Stmt.Assign(s): s.format(tokens)
            Stmt.Expr(s): s.format(tokens)
            Stmt.For(s): s.format(tokens)
            Stmt.While(s): s.format(tokens)
            Stmt.Loop(s): s.format(tokens)
            Stmt.Break(s): s.format(tokens)
            Stmt.Continue(s): s.format(tokens),
    )


LetStmt.format(self: FmtLetStmt, tokens: Array[Token]) Doc:
    let let_ = prevNonTrivia(self.lhs.firstToken(tokens), tokens).unwrap()
    assert(tokens.get(let_.idx).kind is TokenKind.Let)

    let doc = formatToken(let_, tokens) + Doc.blank(1) + self.lhs.format(tokens)

    if self.ty is Option.Some(ty):
        let colon = prevNonTrivia(ty.firstToken(tokens), tokens).unwrap()
        assert(tokens.get(colon.idx).kind is TokenKind.Colon)

        doc += formatToken(colon, tokens) + Doc.blank(1) + ty.format(tokens)

    let eq = prevNonTrivia(self.rhs.firstToken(tokens), tokens).unwrap()
    assert(tokens.get(eq.idx).kind is TokenKind.Eq)

    doc
        + Doc.blank(1)
        + formatToken(eq, tokens)
        + Doc.blank(1)
        + self.rhs.format(tokens)


AssignStmt.format(self: FmtAssignStmt, tokens: Array[Token]) Doc:
    let op = nextNonTrivia(self.lhs.lastToken(tokens), tokens).unwrap()

    self.lhs.format(tokens)
        + Doc.blank(1)
        + formatToken(op, tokens)
        + Doc.blank(1)
        + self.rhs.format(tokens)


ForStmt.format(self: FmtForStmt, tokens: Array[Token]) Doc:
    let doc0 = Doc.empty()
    let for_ = self.firstToken(tokens)

    if self.label is Option.Some(label):
        doc0 += formatToken(label.token, tokens) + Doc.blank(1)
        for_ = nextNonTrivia(label.token, tokens).unwrap()

    assert(tokens.get(for_.idx).kind is TokenKind.For)

    doc0 += formatToken(for_, tokens) + Doc.blank(1)

    let docRest = self.pat.format(tokens)
    let lastToken = self.pat.lastToken(tokens)

    match self.astTy:
        Option.Some(ty):
            let colon = prevNonTrivia(ty.firstToken(tokens), tokens).unwrap()
            assert(tokens.get(colon.idx).kind is TokenKind.Colon)

            docRest += formatToken(colon, tokens)
                + Doc.blank(1)
                + ty.format(tokens)
                + Doc.blank(1)
            lastToken = ty.lastToken(tokens)

        Option.None: docRest += Doc.blank(1)

    let in_ = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(in_.idx).kind is TokenKind.In)

    let colon = nextNonTrivia(self.expr.lastToken(tokens), tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    docRest += Doc.nested(
        4,
        formatToken(in_, tokens)
            + Doc.break_(1)
            + self.expr.format(tokens)
            + formatToken(colon, tokens),
    )

    doc0
        + Doc.nested(
            4,
            docRest.group() + Doc.hardLine() + formatStmts(self.body, tokens),
        )


WhileStmt.format(self: FmtWhileStmt, tokens: Array[Token]) Doc:
    let doc0 = Doc.empty()
    let while_ = self.firstToken(tokens)

    if self.label is Option.Some(label):
        doc0 += formatToken(label.token, tokens) + Doc.blank(1)
        while_ = nextNonTrivia(label.token, tokens).unwrap()

    assert(tokens.get(while_.idx).kind is TokenKind.While)

    doc0 += formatToken(while_, tokens) + Doc.blank(1)

    let colon = nextNonTrivia(self.cond.lastToken(tokens), tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    doc0
        + Doc.nested(
            4,
            self.cond.format(tokens)
                + formatToken(colon, tokens)
                + Doc.hardLine()
                + formatStmts(self.body, tokens),
        )


LoopStmt.format(self: FmtLoopStmt, tokens: Array[Token]) Doc:
    let loop_ = self.firstToken(tokens)

    let colon = nextNonTrivia(loop_, tokens).unwrap()
    assert(tokens.get(colon.idx).kind is TokenKind.Colon)

    formatToken(loop_, tokens)
        + Doc.nested(
            4,
            formatToken(colon, tokens)
                + Doc.hardLine()
                + formatStmts(self.body, tokens),
        )


BreakStmt.format(self, tokens: Array[Token]) Doc:
    let break_ = self.firstToken(tokens)

    match self.label:
        Option.None: formatToken(break_, tokens)

        Option.Some(label):
            formatToken(break_, tokens)
                + Doc.nested(
                    4, Doc.break_(1) + formatToken(label.token, tokens)
                )


ContinueStmt.format(self, tokens: Array[Token]) Doc:
    let continue_ = self.firstToken(tokens)

    match self.label:
        Option.None: formatToken(continue_, tokens)

        Option.Some(label):
            formatToken(continue_, tokens)
                + Doc.nested(
                    4, Doc.break_(1) + formatToken(label.token, tokens)
                )


# --------------------------------------------------------------------------------------------------
# Types


Type.format(self: FmtType, tokens: Array[Token]) Doc:
    match self:
        Type.Named(t): t.format(tokens)
        Type.Var(id): formatToken(id.token, tokens)
        Type.Record(t): t.format(tokens)
        Type.Variant(t): t.format(tokens)
        Type.Fn_(t): t.format(tokens)
        Type.AssocTySelect(t): t.format(tokens)


NamedType.format(self: FmtNamedType, tokens: Array[Token]) Doc:
    formatToken(self.name.token, tokens) + formatTyArgs(self.args, tokens)


RecordType.format(self: FmtRecordType, tokens: Array[Token]) Doc:
    let lparen = self.firstToken(tokens)
    assert(
        tokens.get(lparen.idx).kind is TokenKind.LParen | TokenKind.LParenRow
    )

    let doc0 = formatToken(lparen, tokens)
    let docRest = Doc.empty()

    let trailingComma = Bool.False
    let lastToken = lparen
    for field: Named[FmtType] in self.fields.iter():
        if trailingComma:
            docRest += Doc.blank(1)
            trailingComma = Bool.False

        docRest += formatNamed(field, Type.format, tokens)
        lastToken = field.lastToken(tokens)

        if nextNonTrivia(field.lastToken(tokens), tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            docRest += formatToken(next, tokens)
            lastToken = next

    if self.extension is Option.Some(ext):
        let dotdot = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)

        if trailingComma:
            docRest += Doc.blank(1)

        docRest += formatToken(dotdot, tokens) + ext.format(tokens)

    let rparen = self.lastToken(tokens)
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    doc0 + Doc.grouped(docRest + formatToken(rparen, tokens))


VariantType.format(self: FmtVariantType, tokens: Array[Token]) Doc:
    let lbracket = self.firstToken(tokens)
    assert(
        tokens.get(lbracket.idx).kind
            is TokenKind.LBracket | TokenKind.LBracketRow,
    )

    let rbracket = self.lastToken(tokens)
    assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

    let doc0 = formatToken(lbracket, tokens)
    let docRest = Doc.empty()

    let trailingComma = Bool.False
    let lastToken = lbracket
    for alt: FmtNamedType in self.alts.iter():
        if trailingComma:
            docRest += Doc.blank(1)
            trailingComma = Bool.False

        docRest += alt.format(tokens)

        if nextNonTrivia(alt.lastToken(tokens), tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            docRest += formatToken(next, tokens)
            lastToken = next

    if self.extension is Option.Some(ext):
        if trailingComma:
            docRest += Doc.blank(1)

        let dotdot = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)

        docRest += formatToken(dotdot, tokens) + ext.format(tokens)

    doc0 + docRest + formatToken(rbracket, tokens)


FnType.format(self: FmtFnType, tokens: Array[Token]) Doc:
    let fn_ = self.firstToken(tokens)

    let lparen = nextNonTrivia(fn_, tokens).unwrap()
    assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

    let doc = formatToken(fn_, tokens) + formatToken(lparen, tokens)

    let lastToken = lparen
    let trailingComma = Bool.False
    for arg: FmtType in self.args.iter():
        if trailingComma:
            doc += Doc.blank(1)
            trailingComma = Bool.False

        doc += arg.format(tokens)
        lastToken = arg.lastToken(tokens)

        if nextNonTrivia(lastToken, tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            doc += formatToken(next, tokens)
            lastToken = next

    let rparen = nextNonTrivia(lastToken, tokens).unwrap()
    assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

    lastToken = rparen

    doc += formatToken(rparen, tokens)

    if self.ret is Option.Some(ret):
        doc += Doc.blank(1) + ret.format(tokens)
        lastToken = ret.lastToken(tokens)

    if self.exceptions is Option.Some(exn):
        let slash = nextNonTrivia(lastToken, tokens).unwrap()
        assert(tokens.get(slash.idx).kind is TokenKind.Slash)

        doc += Doc.blank(1)
            + formatToken(slash, tokens)
            + Doc.blank(1)
            + exn.format(tokens)

    doc


AssocTySelectType.format(self: FmtAssocTySelectType, tokens: Array[Token]) Doc:
    let doc = self.ty.format(tokens)
    let dot = nextNonTrivia(self.ty.lastToken(tokens), tokens).unwrap()
    assert(tokens.get(dot.idx).kind is TokenKind.Dot)
    doc + formatToken(dot, tokens) + formatToken(self.assocTy.token, tokens)


# --------------------------------------------------------------------------------------------------
# Patterns


Pat.format(self: FmtPat, tokens: Array[Token]) Doc:
    match self:
        Pat.Var(p): p.format(tokens)

        Pat.Con(p): p.format(tokens)

        Pat.Record(p): p.format(tokens)

        Pat.Ignore(p) | Pat.Char(_, p): formatToken(p, tokens)

        Pat.Str(_, p):
            formatToken(p, tokens) + formatToken(self.lastToken(tokens), tokens)

        Pat.Or(ps):
            # Same formatting as binary operators.
            let doc0 = ps.get(0).format(tokens)

            let docRest = Doc.empty()
            for p: FmtPat in ps.iter().skip(1):
                let pipe = prevNonTrivia(p.firstToken(tokens), tokens).unwrap()
                assert(tokens.get(pipe.idx).kind is TokenKind.Pipe)

                docRest += Doc.break_(1)
                    + formatToken(pipe, tokens)
                    + Doc.blank(1)
                    + p.format(tokens)

            Doc.grouped(doc0 + docRest.nest(4))

        Pat.Variant(p): p.format(tokens)


VarPat.format(self, tokens: Array[Token]) Doc:
    formatToken(self.var_.token, tokens)


ConPat.format(self: FmtConPat, tokens: Array[Token]) Doc:
    let con = self.con.format(tokens)

    if self.fields.isEmpty() and self.rest is RestPat.No:
        return con

    let lparen = nextNonTrivia(self.con.lastToken(tokens), tokens).unwrap()
    assert(tokens.get(lparen.idx).kind is TokenKind.LParen)

    let args = formatToken(lparen, tokens) + Doc.break_(0)

    let trailingComma = Bool.False
    let lastToken = lparen
    for field: Named[FmtPat] in self.fields.iter():
        if trailingComma:
            args += Doc.break_(1)
            trailingComma = Bool.False

        args += formatNamed(field, Pat.format, tokens)
        lastToken = field.lastToken(tokens)

        if nextNonTrivia(field.lastToken(tokens), tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            args += formatToken(next, tokens)
            lastToken = next

    match self.rest:
        RestPat.Ignore:
            if trailingComma:
                args += Doc.break_(1)

            let dotdot = nextNonTrivia(lastToken, tokens).unwrap()
            assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)

            args += formatToken(dotdot, tokens)

        RestPat.Bind(..):
            if trailingComma:
                args += Doc.break_(1)

            let dotdot = nextNonTrivia(lastToken, tokens).unwrap()
            assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)

            let ident = nextNonTrivia(dotdot, tokens).unwrap()
            args += formatToken(dotdot, tokens) + formatToken(ident, tokens)

        RestPat.No:
            if self.fields.len() != 0 and not trailingComma:
                args += Doc.whenNotFlat(Doc.char(','))

    let rparen = self.lastToken(tokens)
    Doc.grouped(
        con
            + Doc.grouped(
                args.nest(4).group()
                    + Doc.break_(0)
                    + formatToken(rparen, tokens),
            ),
    )


RecordPat.format(self: FmtRecordPat, tokens: Array[Token]) Doc:
    let lparen = self.firstToken(tokens)
    let doc = formatToken(lparen, tokens) + Doc.break_(0)

    let trailingComma = Bool.False
    let lastToken = lparen
    for field: Named[FmtPat] in self.fields.iter():
        if trailingComma:
            doc += Doc.break_(1)
            trailingComma = Bool.False

        doc += formatNamed(field, Pat.format, tokens)
        lastToken = field.lastToken(tokens)

        if nextNonTrivia(field.lastToken(tokens), tokens) is Option.Some(next)
                and tokens.get(next.idx).kind is TokenKind.Comma:
            trailingComma = Bool.True
            doc += formatToken(next, tokens)
            lastToken = next

    match self.rest:
        RestPat.Ignore:
            if trailingComma:
                doc += Doc.blank(1)

            let dotdot = nextNonTrivia(lastToken, tokens).unwrap()
            assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)

            doc += formatToken(dotdot, tokens)

        RestPat.Bind(..):
            if trailingComma:
                doc += Doc.blank(1)

            let dotdot = nextNonTrivia(lastToken, tokens).unwrap()
            assert(tokens.get(dotdot.idx).kind is TokenKind.DotDot)

            let ident = nextNonTrivia(dotdot, tokens).unwrap()
            doc += formatToken(dotdot, tokens) + formatToken(ident, tokens)

        RestPat.No:
            if not trailingComma:
                doc += Doc.whenNotFlat(Doc.char(','))

    let rparen = self.lastToken(tokens)
    Doc.grouped(doc.nest(4) + Doc.break_(0) + formatToken(rparen, tokens))


VariantPat.format(self: FmtVariantPat, tokens: Array[Token]) Doc:
    let tilde = prevNonTrivia(self.pat.firstToken(tokens), tokens).unwrap()
    assert(tokens.get(tilde.idx).kind is TokenKind.Tilde)
    formatToken(tilde, tokens) + self.pat.format(tokens)


Attribute.format(self: FmtAttribute, tokens: Array[Token]) Doc:
    formatToken(self.open, tokens)
        + self.expr.format(tokens)
        + formatToken(self.close, tokens)


# --------------------------------------------------------------------------------------------------


## Format a single token, handling comment tokens that are
##      (1) before the token, that are not with other tokens in their lines.
##      (2) after the token, at the same line with the token being formatted.
formatToken(tokenIdx: TokenIdx, tokens: Array[Token]) Doc:
    formatLeadingComments(tokenIdx, tokens)
        + Doc.str(tokens.get(tokenIdx.idx).text)
        + formatTrailingComments(tokenIdx, tokens)


formatLeadingComments(tokenIdx: TokenIdx, tokens: Array[Token]) Doc:
    let doc = Doc.empty()

    if findCommentBefore(tokenIdx, tokens) is Option.Some(commentStart):
        let token = tokens.get(tokenIdx.idx)

        let maxEmptyLines: U32 = if token.col == 0:
            2
        else:
            1

        let leading = formatLeadingComments_(
            commentStart, tokenIdx, maxEmptyLines, tokens,
        )
        doc += leading.doc
        let lastCommentToken = tokens.get(leading.lastCommentIdx.idx)

        # Keep empty lines between the last comment token and the token being formatted.
        let lastCommentTokenLine = lastCommentToken.rightLoc().line
        if token.line != lastCommentTokenLine:
            let emptyLines = token.line - lastCommentTokenLine - 1
            if emptyLines > maxEmptyLines:
                emptyLines = maxEmptyLines

            for _: U32 in range(u32(0), emptyLines):
                doc += Doc.hardLine()

    doc


formatLeadingComments_(
    commentStart: TokenIdx,
    commentEnd: TokenIdx,
    maxEmptyLines: U32,
    tokens: Array[Token],
) (doc: Doc, lastCommentIdx: TokenIdx):
    let doc = Doc.empty()

    let prevCommentTokenIdx: Option[TokenIdx] = Option.None
    for commentTokenIdx: TokenIdx in range(commentStart, commentEnd):
        let commentToken = tokens.get(commentTokenIdx.idx)

        if commentToken.isSpace():
            continue

        # Keep empty lines between comments.
        if prevCommentTokenIdx is Option.Some(prevCommentTokenIdx):
            let prevCommentToken = tokens.get(prevCommentTokenIdx.idx)
            let prevCommentTokenLine = prevCommentToken.rightLoc().line
            if commentToken.line != prevCommentTokenLine:
                let emptyLines = commentToken.line - prevCommentTokenLine - 1
                if emptyLines > maxEmptyLines:
                    emptyLines = maxEmptyLines

                for _: U32 in range(u32(0), emptyLines):
                    doc += Doc.hardLine()

        doc += Doc.str(commentToken.text) + Doc.hardLine()

        prevCommentTokenIdx = Option.Some(commentTokenIdx)

    (doc = doc, lastCommentIdx = prevCommentTokenIdx.unwrap())


formatTrailingComments(tokenIdx: TokenIdx, tokens: Array[Token]) Doc:
    let doc = Doc.empty()
    let token = tokens.get(tokenIdx.idx)
    let tokenLastLine = token.rightLoc().line
    let trailingTokenIdx = tokenIdx.idx + 1
    while tokens.getOpt(trailingTokenIdx) is Option.Some(nextToken):
        if nextToken.isSpace():
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


formatTyArgs(tyArgs: Option[FmtTyArgs], tokens: Array[Token]) Doc:
    match tyArgs:
        Option.None: Doc.empty()

        Option.Some(tyArgs):
            let lbracket = tyArgs.firstToken(tokens)
            assert(tokens.get(lbracket.idx).kind is TokenKind.LBracket)

            let rbracket = tyArgs.lastToken(tokens)
            assert(tokens.get(rbracket.idx).kind is TokenKind.RBracket)

            let doc = formatToken(lbracket, tokens)

            let trailingComma = Bool.False
            for tyArg: FmtType in tyArgs.args.iter():
                if trailingComma:
                    doc += Doc.blank(1)
                    trailingComma = Bool.False

                doc += tyArg.format(tokens)

                if nextNonTrivia(tyArg.lastToken(tokens), tokens)
                        is Option.Some(next)
                        and tokens.get(next.idx).kind is TokenKind.Comma:
                    trailingComma = Bool.True
                    doc += formatToken(next, tokens)

            doc + formatToken(rbracket, tokens)


formatNamed(
    named: Named[a],
    format: Fn(a, Array[Token]) Doc / exn,
    tokens: Array[Token],
) Doc / exn:
    match named.name:
        Option.None: format(named.node, tokens)

        Option.Some(name):
            let op = nextNonTrivia(name.token, tokens).unwrap()
            let opToken = tokens.get(op.idx)
            let opKind = opToken.kind
            assert(opKind is TokenKind.Eq | TokenKind.Colon)

            Doc.nested(
                4,
                formatToken(name.token, tokens)
                    + (if opKind is TokenKind.Eq:
                        Doc.blank(1)
                    else:
                        Doc.empty())
                    + formatToken(op, tokens)
                    # We can't have a line break after `:` as that starts a new block.
                    + (if opKind is TokenKind.Eq:
                        Doc.break_(1)
                    else:
                        Doc.blank(1))
                    + format(named.node, tokens),
            ).group()


idText(id: Id, tokens: Array[Token]) Str:
    tokens.get(id.token.idx).text


tokenText(token: TokenIdx, tokens: Array[Token]) Str:
    tokens.get(token.idx).text


join[Iterator[iter, exn], Iterator[iter, exn].Item = Doc](iter: iter, sep: Doc) Doc / exn:
    let doc = match iter.next():
        Option.None: return Doc.empty()
        Option.Some(doc): doc

    for d: Doc in iter:
        doc += sep + d

    doc


# --------------------------------------------------------------------------------------------------


## Find the beginning of comment tokens before `token` that belong to `token`.
findCommentBefore(token: TokenIdx, tokens: Array[Token]) Option[TokenIdx]:
    let idx = token.idx
    let commentStart: Option[TokenIdx] = Option.None

    while idx != 0:
        let prev = tokens.get(idx - 1)

        if prev.isSpace():
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
commentAtStart(tokenIdx: TokenIdx, tokens: Array[Token]) Bool:
    let idx = tokenIdx.idx

    if idx == 0:
        return Bool.True

    idx -= 1

    while idx != 0:
        let prev = tokens.get(idx)

        if prev.isSpaceOrComment():
            idx -= 1
            continue

        break

    if idx == 0 and tokens.get(idx).isSpaceOrComment():
        return Bool.True

    tokens.get(idx).line != tokens.get(tokenIdx.idx).line


# --------------------------------------------------------------------------------------------------


type FmtTopDecl = TopDecl[DefaultAstExts]


type FmtTypeDecl = TypeDecl[DefaultAstExts]


type FmtTypeDeclRhs = TypeDeclRhs[DefaultAstExts]


type FmtConDecl = ConDecl[DefaultAstExts]


type FmtConFields = ConFields[DefaultAstExts]


type FmtNamedField = NamedField[DefaultAstExts]


type FmtFunDecl = FunDecl[DefaultAstExts]


type FmtFunArg = FunArg[DefaultAstExts]


type FmtTraitDecl = TraitDecl[DefaultAstExts]


type FmtTraitDeclItem = TraitDeclItem[DefaultAstExts]


type FmtImplDecl = ImplDecl[DefaultAstExts]


type FmtImplDeclItem = ImplDeclItem[DefaultAstExts]


type FmtType = Type[DefaultAstExts]


type FmtNamedType = NamedType[DefaultAstExts]


type FmtRecordType = RecordType[DefaultAstExts]


type FmtVariantType = VariantType[DefaultAstExts]


type FmtFnType = FnType[DefaultAstExts]


type FmtAssocTySelectType = AssocTySelectType[DefaultAstExts]


type FmtContext = Context[DefaultAstExts]


type FmtPred_ = Pred_[DefaultAstExts]


type FmtDeclTypeParam = DeclTypeParam[DefaultAstExts]


type FmtStmt = Stmt[DefaultAstExts]


type FmtLetStmt = LetStmt[DefaultAstExts]


type FmtAssignStmt = AssignStmt[DefaultAstExts]


type FmtForStmt = ForStmt[DefaultAstExts]


type FmtWhileStmt = WhileStmt[DefaultAstExts]


type FmtLoopStmt = LoopStmt[DefaultAstExts]


type FmtPat = Pat[DefaultAstExts]


type FmtConPat = ConPat[DefaultAstExts]


type FmtRecordPat = RecordPat[DefaultAstExts]


type FmtVariantPat = VariantPat[DefaultAstExts]


type FmtCon = Con[DefaultAstExts]


type FmtExpr = Expr[DefaultAstExts]


type FmtVarExpr = VarExpr[DefaultAstExts]


type FmtFieldSelExpr = FieldSelExpr[DefaultAstExts]


type FmtAssocFnSelExpr = AssocFnSelExpr[DefaultAstExts]


type FmtCallExpr = CallExpr[DefaultAstExts]


type FmtStrExpr = StrExpr[DefaultAstExts]


type FmtStrPart = StrPart[DefaultAstExts]


type FmtBinOpExpr = BinOpExpr[DefaultAstExts]


type FmtUnOpExpr = UnOpExpr[DefaultAstExts]


type FmtRecordExpr = RecordExpr[DefaultAstExts]


type FmtVariantExpr = VariantExpr[DefaultAstExts]


type FmtReturnExpr = ReturnExpr[DefaultAstExts]


type FmtMatchExpr = MatchExpr[DefaultAstExts]


type FmtAlt = Alt[DefaultAstExts]


type FmtIfExpr = IfExpr[DefaultAstExts]


type FmtIfBranch = IfBranch[DefaultAstExts]


type FmtFnExpr = FnExpr[DefaultAstExts]


type FmtIsExpr = IsExpr[DefaultAstExts]


type FmtDoExpr = DoExpr[DefaultAstExts]


type FmtSeqExpr = SeqExpr[DefaultAstExts]


type FmtSeqElem = SeqElem[DefaultAstExts]


type FmtParenExpr = ParenExpr[DefaultAstExts]


type FmtAttribute = Attribute[DefaultAstExts]


type FmtTyArgs = TyArgs[DefaultAstExts]
