# This is generated file, do not edit.

import [
    Compiler/Interpolation2,
    Compiler/ParseUtils2,
    Compiler/Token,
    Tool/Peg/ParseTree,
]


module[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Vec[TopDecl[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let zeroOrMoreCursor0 = state._cursor
            let ds = Vec.empty()
            loop:
                let dsLen0 = ds.len()
                let symResult = try(\(): ds.push(topDecl(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ds.truncate(dsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.None:
                state._cursor
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                ds
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


topDecl[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) TopDecl[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let t = typeDecl(state)
            let val = do:
                TopDecl.Type(t)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let t = importDecl(state)
            let val = do:
                TopDecl.Import(t)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let t = traitDecl(state)
            let val = do:
                TopDecl.Trait(t)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let t = implDecl(state)
            let val = do:
                TopDecl.Impl(t)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let t = topFunDecl(state)
            let val = do:
                TopDecl.Fun(t)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


type_[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Type[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let t = namedType(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Dot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let selection = state.nextCursor()
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.UpperId, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    selection,
            )
            let selection = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                match selection:
                    Option.None: Type.Named(t)
                    Option.Some(selection):
                        Type.AssocTySelect(
                            AssocTySelectType(
                                ty = Type.Named(t), assocTy = newId(selection)
                            ),
                        )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let id = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Type.Var(newId(id))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let t = recordType(state)
            let val = do:
                Type.Record(t)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let t = variantType(state)
            let val = do:
                Type.Variant(t)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let t = fnType(state)
            let val = do:
                Type.Fn_(t)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


namedType[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) NamedType[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let argFirst = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let arg0 = type_(state)
            let zeroOrMoreCursor0 = state._cursor
            let args = Vec.empty()
            loop:
                let argsLen0 = args.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        args.push(type_(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        args.truncate(argsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let argLast = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let args = Vec.fromIter(once(arg0).chain(args.iter()))
                NamedType(
                    name = newTyId(name),
                    args =
                        Option.Some(
                            TyArgs(
                                args,
                                _firstToken = TokenIdx(idx = argFirst),
                                _lastToken = TokenIdx(idx = argLast),
                            ),
                        ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                NamedType(name = newTyId(name), args = Option.None)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


recordType[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) RecordType[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let start = recordTypeStart(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                RecordType(
                    fields = Vec.empty(),
                    extension = Option.None,
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let start = recordTypeStart(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let ext = type_(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                RecordType(
                    fields = Vec.empty(),
                    extension = Option.Some(ext),
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let start = recordTypeStart(state)
            let f0 = recordTypeField(state)
            let zeroOrMoreCursor0 = state._cursor
            let fs = Vec.empty()
            loop:
                let fsLen0 = fs.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        fs.push(recordTypeField(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        fs.truncate(fsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ext = recordTypeCont(state)
                    ext,
            )
            let ext = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let fields: Vec[Named[Type[exts]]] = Vec.fromIter(
                    once(f0).chain(fs.iter())
                )
                RecordType(
                    fields,
                    extension = ext.flatten(),
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


recordTypeStart(state: ParserState[Token, ()]) (start: TokenIdx, isRow: Bool) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let start = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (start = TokenIdx(idx = start), isRow = Bool.False)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let start = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParenRow, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (start = TokenIdx(idx = start), isRow = Bool.True)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


recordTypeCont[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Option[Type[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.DotDot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let ext = type_(state)
                    ext,
            )
            let ext = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                ext
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


variantType[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) VariantType[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let start = variantTypeStart(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                VariantType(
                    alts = Vec.empty(),
                    extension = Option.None,
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let start = variantTypeStart(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let ext = type_(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                VariantType(
                    alts = Vec.empty(),
                    extension = Option.Some(ext),
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let start = variantTypeStart(state)
            let alt0 = namedType(state)
            let zeroOrMoreCursor0 = state._cursor
            let alts = Vec.empty()
            loop:
                let altsLen0 = alts.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        alts.push(namedType(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        alts.truncate(altsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ext = variantTypeCont(state)
                    ext,
            )
            let ext = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                VariantType(
                    alts = Vec.fromIter(once(alt0).chain(alts.iter())),
                    extension = ext.flatten(),
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


variantTypeStart(state: ParserState[Token, ()]) (start: TokenIdx, isRow: Bool) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let start = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (start = TokenIdx(idx = start), isRow = Bool.False)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let start = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracketRow, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (start = TokenIdx(idx = start), isRow = Bool.True)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


variantTypeCont[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Option[Type[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.DotDot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let ext = type_(state)
                    ext,
            )
            let ext = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                ext
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


recordTypeField[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Named[Type[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let ty = type_(state)
            let val = do:
                Named(name = Option.Some(newId(name)), node = ty)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let ty = type_(state)
            let val = do:
                Named(name = Option.None, node = ty)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


fnType[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) FnType[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperFn, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let args = fnArgTys(state)
                    args,
            )
            let args = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let rparen = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ret = returnTy(state)
                    ret,
            )
            let ret = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                let args = args.unwrapOr(Vec.empty())
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                FnType(
                    args,
                    ret = ret.ret,
                    exceptions = ret.exn,
                    _firstToken = TokenIdx(idx = first),
                    _rparen = TokenIdx(idx = rparen),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


fnArgTys[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Vec[Type[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let t0 = type_(state)
            let zeroOrMoreCursor0 = state._cursor
            let ts = Vec.empty()
            loop:
                let tsLen0 = ts.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ts.push(type_(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ts.truncate(tsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let val = do:
                let vec: Vec[Type[exts]] = Vec.fromIter(
                    once(t0).chain(ts.iter())
                )
                vec
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


returnTy[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) (ret: Option[Type[exts]], exn: Option[Type[exts]]) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let ret = type_(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Slash, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let exn = type_(state)
            let val = do:
                (ret = Option.Some(ret), exn = Option.Some(exn))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let ret = type_(state)
            let val = do:
                (ret = Option.Some(ret), exn = Option.None)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Slash, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let exn = type_(state)
            let val = do:
                (ret = Option.None, exn = Option.Some(exn))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


typeDecl[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) TypeDecl[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let attr = attr(state)
                    attr,
            )
            let attr = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let valToken = if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Value, ..):
                        state._cursor += 1
                        sym
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    valToken,
            )
            let valToken = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Type, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.LBracket, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let params = typeParams(state)
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.RBracket, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    params,
            )
            let params = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            let rhs = Vec.empty()
            loop:
                let rhsLen0 = rhs.len()
                let symResult = try(\(): rhs.push(conDecl(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        rhs.truncate(rhsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.DotDot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let ext = type_(state)
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Newline, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    ext,
            )
            let ext = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                TypeDecl(
                    attr,
                    value_ = valToken.map(\(a): TokenIdx(idx = val)),
                    prim_ = Option.None,
                    name = newId(name),
                    rhs =
                        Option.Some(
                            TypeDeclRhs.Sum(cons = rhs, extension = ext)
                        ),
                    typeParams =
                        match params:
                            Option.Some(params): params
                            Option.None: Vec.empty(),
                    ..AstExts[exts].defaultTypeDeclExts()
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let attr = attr(state)
                    attr,
            )
            let attr = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let valToken = if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Value, ..):
                        state._cursor += 1
                        sym
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    valToken,
            )
            let valToken = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Type, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.LBracket, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let params = typeParams(state)
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.RBracket, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    params,
            )
            let params = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let fs = conFields(state)
                    fs,
            )
            let fs = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let fs = match fs:
                    Option.Some(fs): fs.fields
                    Option.None: ConFields.Empty
                TypeDecl(
                    attr,
                    value_ = valToken.map(\(a): TokenIdx(idx = val)),
                    prim_ = Option.None,
                    name = newId(name),
                    rhs = Option.Some(TypeDeclRhs.Product(fs)),
                    typeParams =
                        match params:
                            Option.Some(params): params
                            Option.None: Vec.empty(),
                    ..AstExts[exts].defaultTypeDeclExts()
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let val = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Type, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let params = typeParams(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Eq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let rhs = type_(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                TypeDecl(
                    attr = Option.None,
                    value_ = Option.None,
                    prim_ = Option.None,
                    name = newId(name),
                    rhs = Option.Some(TypeDeclRhs.Synonym(rhs)),
                    typeParams = params,
                    ..AstExts[exts].defaultTypeDeclExts()
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let val = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Type, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Eq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let rhs = type_(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                TypeDecl(
                    attr = Option.None,
                    value_ = Option.None,
                    prim_ = Option.None,
                    name = newId(name),
                    rhs = Option.Some(TypeDeclRhs.Synonym(rhs)),
                    typeParams = Vec.empty(),
                    ..AstExts[exts].defaultTypeDeclExts()
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let prim_ = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Prim, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Type, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.LBracket, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let params = typeParams(state)
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.RBracket, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    params,
            )
            let params = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                TypeDecl(
                    attr = Option.None,
                    value_ = Option.None,
                    prim_ = Option.Some(TokenIdx(idx = prim_)),
                    name = newId(name),
                    rhs = Option.None,
                    typeParams =
                        match params:
                            Option.Some(params): params
                            Option.None: Vec.empty(),
                    ..AstExts[exts].defaultTypeDeclExts()
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


typeParams[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Vec[DeclTypeParam[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let p0 = declTypeParam(state)
            let zeroOrMoreCursor0 = state._cursor
            let ps = Vec.empty()
            loop:
                let psLen0 = ps.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ps.push(declTypeParam(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ps.truncate(psLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let val = do:
                Vec.fromIter(once(p0).chain(ps.iter()))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


declTypeParam[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) DeclTypeParam[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Colon, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let kind = type_(state)
                    kind,
            )
            let kind = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                DeclTypeParam(name = newId(name), kind)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


conDecl[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) ConDecl[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let fs = conFields(state)
                    fs,
            )
            let fs = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let name = newId(name)
                match fs:
                    Option.Some(fs):
                        ConDecl(
                            name, fields = fs.fields, _lastToken = fs.lastToken,
                        )
                    Option.None:
                        ConDecl(
                            name,
                            fields = ConFields.Empty,
                            _lastToken = name.token,
                        )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


conFields[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) (fields: ConFields[exts], lastToken: TokenIdx) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (fields = ConFields.Empty, lastToken = TokenIdx(idx = last))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let f0 = conField(state)
            let zeroOrMoreCursor0 = state._cursor
            let fs = Vec.empty()
            loop:
                let fsLen0 = fs.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        fs.push(conField(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        fs.truncate(fsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.DotDot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let ext = type_(state)
                    ext,
            )
            let ext = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let vec: Vec[(name: Option[Id], ty: Type[exts])] = Vec.fromIter(
                    once(f0).chain(fs.iter())
                )
                (
                    fields = processFields(vec, ext),
                    lastToken = TokenIdx(idx = last),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let ext = type_(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (
                    fields = processFields(Vec.empty(), Option.Some(ext)),
                    lastToken = TokenIdx(idx = last),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


conField[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) (name: Option[Id], ty: Type[exts]) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let name = state.nextCursor()
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.LowerId, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Colon, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    name,
            )
            let name = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let ty = type_(state)
            let val = do:
                (name = name.map(\(name: U32): newId(name)), ty = ty)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


expr[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Expr[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let e = inlineExpr(state)
            let val = do:
                e
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let e = blockExpr(state)
            let val = do:
                e
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


inlineExpr[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Expr[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let expr = prefixExpr(state)
            let zeroOrMoreCursor0 = state._cursor
            let cont = Vec.empty()
            loop:
                let contLen0 = cont.len()
                let symResult = try(\(): cont.push(inlineExprCont(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        cont.truncate(contLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let val = do:
                associate(expr, cont)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


blockExpr[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Expr[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Match, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let scrut = inlineExpr(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let alts = Vec.empty()
            alts.push(matchAlt(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let altsLen0 = alts.len()
                let symResult = try(\(): alts.push(matchAlt(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        alts.truncate(altsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Expr.Match(
                    MatchExpr(
                        scrutinee = scrut,
                        alts,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.If, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let cond0 = inlineExpr(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body0 = Vec.empty()
            body0.push(stmt(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let body0Len0 = body0.len()
                let symResult = try(\(): body0.push(stmt(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        body0.truncate(body0Len0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            let conds = Vec.empty()
            loop:
                let condsLen0 = conds.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Elif, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        let cond = inlineExpr(state)
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Colon, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Newline, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Indent, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        let body = Vec.empty()
                        body.push(stmt(state))
                        let zeroOrMoreCursor0 = state._cursor
                        loop:
                            let bodyLen0 = body.len()
                            let symResult = try(\(): body.push(stmt(state)))
                            match symResult:
                                Result.Err(err):
                                    state._cursor = zeroOrMoreCursor0
                                    body.truncate(bodyLen0)
                                    break
                                Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Dedent, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        conds.push((cond = cond, body = body)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        conds.truncate(condsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Else, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Colon, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Newline, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Indent, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let else_ = Vec.empty()
                    else_.push(stmt(state))
                    let zeroOrMoreCursor0 = state._cursor
                    loop:
                        let else_Len0 = else_.len()
                        let symResult = try(\(): else_.push(stmt(state)))
                        match symResult:
                            Result.Err(err):
                                state._cursor = zeroOrMoreCursor0
                                else_.truncate(else_Len0)
                                break
                            Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Dedent, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    else_,
            )
            let else_ = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                Expr.If(
                    IfExpr(
                        _firstToken = TokenIdx(idx = cur),
                        branches =
                            Vec.fromIter(
                                once(IfBranch(guard = cond0, body = body0))
                                    .chain(
                                    conds.iter().map(
                                        \(branch: (cond: Expr[exts], body: Vec[Stmt[exts]])):
                                            IfBranch(
                                                guard = branch.cond,
                                                body = branch.body,
                                            ),
                                    ),
                                ),
                            ),
                        elseBranch = else_,
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Do, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body = Vec.empty()
            body.push(stmt(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let bodyLen0 = body.len()
                let symResult = try(\(): body.push(stmt(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        body.truncate(bodyLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Expr.Do(DoExpr(body, _firstToken = TokenIdx(idx = cur)))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.BackslashLParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let args = fnArgs(state)
                    args,
            )
            let args = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ret = returnTy(state)
                    ret,
            )
            let ret = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body = Vec.empty()
            body.push(stmt(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let bodyLen0 = body.len()
                let symResult = try(\(): body.push(stmt(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        body.truncate(bodyLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                Expr.Fn_(
                    FnExpr(
                        sig =
                            FunSig(
                                context = Option.None,
                                self_ = SelfParam.No,
                                params = args.unwrapOr(Vec.empty()),
                                exceptions = ret.exn,
                                returnTy = ret.ret,
                                lparen = TokenIdx(idx = cur),
                                ..AstExts[exts].defaultFunSigExts()
                            ),
                        body,
                        idx = 0,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


inlineExprCont[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) InlineExprCont[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let op = binOp(state)
            let rhs = prefixExpr(state)
            let val = do:
                InlineExprCont.BinOp(op, rhs)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Is, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let pat = pat(state)
            let val = do:
                InlineExprCont.Is(pat)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


prefixExpr[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Expr[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let pfx = exprPrefix(state)
                    pfx,
            )
            let pfx = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let expr = simpleExpr(state)
            let zeroOrMoreCursor0 = state._cursor
            let suffix = Vec.empty()
            loop:
                let suffixLen0 = suffix.len()
                let symResult = try(\(): suffix.push(exprSuffix(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        suffix.truncate(suffixLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let val = do:
                let ret = expr
                for suffix_ in suffix.iter():
                    match suffix_:
                        ExprSuffix.Field(field, tyArgs):
                            ret = Expr.FieldSel(
                                FieldSelExpr(
                                    object = ret, field, userTyArgs = tyArgs,
                                ),
                            )
                        ExprSuffix.Args(args, splice, _lastToken):
                            ret = Expr.Call(
                                CallExpr(fun = ret, args, splice, _lastToken)
                            )
                if pfx is Option.Some(pfx):
                    match pfx:
                        ExprPrefix.Tilde(token):
                            ret = Expr.Variant(
                                VariantExpr(
                                    expr = ret,
                                    ..AstExts[exts].defaultInferredTyExts()
                                ),
                            )
                        ExprPrefix.Minus(token):
                            ret = Expr.UnOp(
                                UnOpExpr(
                                    op = UnOp.Neg,
                                    expr = ret,
                                    _firstToken = token,
                                ),
                            )
                        ExprPrefix.Not(token):
                            ret = Expr.UnOp(
                                UnOpExpr(
                                    op = UnOp.Not,
                                    expr = ret,
                                    _firstToken = token,
                                ),
                            )
                ret
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


exprSuffix[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) ExprSuffix[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let field = field(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let args = tyArgs(state)
                    args,
            )
            let args = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                ExprSuffix.Field(field, tyArgs = args)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let args = args(state)
            let val = do:
                ExprSuffix.Args(
                    args = args.args,
                    splice = args.splice,
                    _lastToken = TokenIdx(idx = args.cursorRight),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


field(state: ParserState[Token, ()]) Id / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let field = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                newId(field)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


args[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) (args: Vec[Named[Expr[exts]]], splice: Option[Expr[exts]], cursorRight: U32) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let splice = inlineExpr(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (
                    args = Vec.empty(),
                    splice = Option.Some(splice),
                    cursorRight = last,
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let arg0 = arg(state)
            let zeroOrMoreCursor0 = state._cursor
            let args = Vec.empty()
            loop:
                let argsLen0 = args.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        args.push(arg(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        args.truncate(argsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let args = (arg0 = arg0, args = args)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let splice = inlineExpr(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (
                    args = Vec.fromIter(once(args.arg0).chain(args.args.iter())),
                    splice = Option.Some(splice),
                    cursorRight = last,
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let arg0 = arg(state)
                    let zeroOrMoreCursor0 = state._cursor
                    let args = Vec.empty()
                    loop:
                        let argsLen0 = args.len()
                        let symResult = try(
                            \():
                                if state.peek() is Option.Some(sym)
                                        and sym
                                            is Token(kind = TokenKind.Comma, ..):
                                    state._cursor += 1
                                else:
                                    throw(
                                        state.updateErrorCursor(state._cursor)
                                    )
                                args.push(arg(state)),
                        )
                        match symResult:
                            Result.Err(err):
                                state._cursor = zeroOrMoreCursor0
                                args.truncate(argsLen0)
                                break
                            Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
                    let optionalCursor0 = state._cursor
                    let symResult = try(
                        \():
                            if state.peek() is Option.Some(sym)
                                    and sym is Token(kind = TokenKind.Comma, ..):
                                state._cursor += 1
                            else:
                                throw(state.updateErrorCursor(state._cursor))
                            (),
                    )
                    match symResult:
                        Result.Err(err): state._cursor = optionalCursor0
                        Result.Ok(ok): ()
                    let args = (arg0 = arg0, args = args)
                    args,
            )
            let args = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (
                    args =
                        match args:
                            Option.None: Vec.empty()
                            Option.Some((arg0, args)):
                                let vec: Vec[Named[Expr[exts]]] = Vec.fromIter(
                                    once(arg0).chain(args.iter())
                                )
                                vec,
                    splice = Option.None,
                    cursorRight = last,
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


arg[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Named[Expr[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Eq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let expr = expr(state)
            let val = do:
                Named(name = Option.Some(newId(name)), node = expr)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let expr = expr(state)
            let val = do:
                Named(name = Option.None, node = expr)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


simpleExpr[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Expr[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let seq = sequence(state)
            let val = do:
                seq
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let var_ = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let tyArgs = tyArgs(state)
                    tyArgs,
            )
            let tyArgs = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                Expr.Var(VarExpr(id = newVarId(var_), userTyArgs = tyArgs,))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let con = con(state)
            let val = do:
                Expr.ConSel(con)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let splice = inlineExpr(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Expr.Record(
                    RecordExpr(
                        fields = Vec.empty(),
                        splice = Option.Some(splice),
                        _firstToken = TokenIdx(idx = first),
                        _lastToken = TokenIdx(idx = last),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let e0 = parenExpr(state)
            let zeroOrMoreCursor0 = state._cursor
            let es = Vec.empty()
            loop:
                let esLen0 = es.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        es.push(parenExpr(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        es.truncate(esLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let fields = (e0 = e0, es = es)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let splice = inlineExpr(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Expr.Record(
                    RecordExpr(
                        fields =
                            Vec.fromIter(
                                once(fields.e0).chain(fields.es.iter())
                            ),
                        splice = Option.Some(splice),
                        _firstToken = TokenIdx(idx = first),
                        _lastToken = TokenIdx(idx = last),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let e0 = parenExpr(state)
                    let zeroOrMoreCursor0 = state._cursor
                    let es = Vec.empty()
                    loop:
                        let esLen0 = es.len()
                        let symResult = try(
                            \():
                                if state.peek() is Option.Some(sym)
                                        and sym
                                            is Token(kind = TokenKind.Comma, ..):
                                    state._cursor += 1
                                else:
                                    throw(
                                        state.updateErrorCursor(state._cursor)
                                    )
                                es.push(parenExpr(state)),
                        )
                        match symResult:
                            Result.Err(err):
                                state._cursor = zeroOrMoreCursor0
                                es.truncate(esLen0)
                                break
                            Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
                    let optionalCursor0 = state._cursor
                    let symResult = try(
                        \():
                            let comma = if state.peek() is Option.Some(sym)
                                    and sym is Token(kind = TokenKind.Comma, ..):
                                state._cursor += 1
                                sym
                            else:
                                throw(state.updateErrorCursor(state._cursor))
                            comma,
                    )
                    let comma = match symResult:
                        Result.Err(err):
                            state._cursor = optionalCursor0
                            Option.None
                        Result.Ok(ok):
                            ()
                            Option.Some(ok)
                    let exprs = (e0 = e0, es = es, comma = comma)
                    exprs,
            )
            let exprs = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                match exprs:
                    Option.None:
                        Expr.Record(
                            RecordExpr(
                                fields = Vec.empty(),
                                splice = Option.None,
                                _firstToken = TokenIdx(idx = first),
                                _lastToken = TokenIdx(idx = last),
                            ),
                        )
                    Option.Some(fields):
                        if fields.es.isEmpty()
                                and fields.comma is Option.None
                                and fields.e0.name is Option.None:
                            Expr.Paren(
                                ParenExpr(
                                    expr = fields.e0.node,
                                    _lparen = TokenIdx(idx = first),
                                    _rparen = TokenIdx(idx = last),
                                ),
                            )
                        else:
                            Expr.Record(
                                RecordExpr(
                                    fields =
                                        Vec.fromIter(
                                            once(fields.e0).chain(
                                                fields.es.iter()
                                            ),
                                        ),
                                    splice = Option.None,
                                    _firstToken = TokenIdx(idx = first),
                                    _lastToken = TokenIdx(idx = last),
                                ),
                            )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Return, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let expr = inlineExpr(state)
                    expr,
            )
            let expr = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                Expr.Return(ReturnExpr(expr, _firstToken = TokenIdx(idx = cur)))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.BackslashLParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let args = fnArgs(state)
                    args,
            )
            let args = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ret = returnTy(state)
                    ret,
            )
            let ret = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body = inlineExpr(state)
            let val = do:
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                Expr.Fn_(
                    FnExpr(
                        sig =
                            FunSig(
                                context = Option.None,
                                self_ = SelfParam.No,
                                params = args.unwrapOr(Vec.empty()),
                                exceptions = ret.exn,
                                returnTy = ret.ret,
                                lparen = TokenIdx(idx = cur),
                                ..AstExts[exts].defaultFunSigExts()
                            ),
                        body = Vec.[Stmt.Expr(body)],
                        idx = 0,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            let int = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Int, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let text = int.text
                let intStr = StrBuf.withCapacity(text.len())
                for char: Char in text.chars():
                    if char == '_':
                        continue
                    intStr.push(char)
                Expr.Int(
                    IntExpr(
                        text = intStr.toStr(),
                        suffix = Option.None,
                        radix = 10,
                        parsed = 0,
                        token = TokenIdx(idx = cur),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.BeginStr, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            let interpolations = Vec.empty()
            loop:
                let interpolationsLen0 = interpolations.len()
                let symResult = try(
                    \():
                        let begin = if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.BeginInterpolation,
                                        ..
                                    ):
                            state._cursor += 1
                            sym
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        let expr = expr(state)
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.EndInterpolation,
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        interpolations.push((begin = begin, expr = expr)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        interpolations.truncate(interpolationsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.EndStr, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Expr.Str(
                    StrExpr(
                        parts = strParts(interpolations),
                        first = TokenIdx(idx = first),
                        last = TokenIdx(idx = last),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            let char = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Char, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Expr.Char(
                    CharExpr(
                        char = parseCharLit(char.text),
                        token = TokenIdx(idx = cur),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


sequence[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Expr[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ty = type_(state)
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Dot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    ty,
            )
            let ty = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let elems = seqElems(state)
            let val = do:
                Expr.Seq(
                    SeqExpr(
                        ty,
                        elems = elems.elems,
                        _lbracket = elems.lbracket,
                        _rbracket = elems.rbracket,
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


seqElems[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) (elems: Vec[SeqElem[exts]], lbracket: TokenIdx, rbracket: TokenIdx) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let lbracket = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let rbracket = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (
                    elems = Vec.empty(),
                    lbracket = TokenIdx(idx = lbracket),
                    rbracket = TokenIdx(idx = rbracket),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let lbracket = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let e0 = seqElem(state)
            let zeroOrMoreCursor0 = state._cursor
            let es = Vec.empty()
            loop:
                let esLen0 = es.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        es.push(seqElem(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        es.truncate(esLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let rbracket = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let vec: Vec[SeqElem[exts]] = Vec.fromIter(
                    once(e0).chain(es.iter())
                )
                (
                    elems = vec,
                    lbracket = TokenIdx(idx = lbracket),
                    rbracket = TokenIdx(idx = rbracket),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


seqElem[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) SeqElem[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let e1 = inlineExpr(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Eq, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let e = inlineExpr(state)
                    let e2 = (e = e)
                    e2,
            )
            let e2 = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                match e2:
                    Option.None: SeqElem(key = Option.None, val = e1)
                    Option.Some((e = e2)):
                        SeqElem(key = Option.Some(e1), val = e2)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


con[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Con[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let ty = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Dot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let con = state.nextCursor()
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.UpperId, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    con,
            )
            let con = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let userTyArgs = tyArgs(state)
                    userTyArgs,
            )
            let userTyArgs = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                Con(
                    ty = newTyId(ty),
                    con = con.map(\(con: U32): newId(con)),
                    userTyArgs,
                    _firstToken = TokenIdx(idx = ty),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


tyArgs[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) TyArgs[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let t0 = type_(state)
            let zeroOrMoreCursor0 = state._cursor
            let ts = Vec.empty()
            loop:
                let tsLen0 = ts.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ts.push(type_(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ts.truncate(tsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let ts: Vec[Type[exts]] = Vec.fromIter(
                    once(t0).chain(ts.iter())
                )
                TyArgs(
                    args = ts,
                    _firstToken = TokenIdx(idx = first),
                    _lastToken = TokenIdx(idx = last),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


parenExpr[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Named[Expr[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Eq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let expr = expr(state)
            let val = do:
                Named(name = Option.Some(newId(name)), node = expr)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let expr = expr(state)
            let val = do:
                Named(name = Option.None, node = expr)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


exprPrefix(state: ParserState[Token, ()]) ExprPrefix / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Tilde, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                ExprPrefix.Tilde(TokenIdx(idx = cur))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Minus, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                ExprPrefix.Minus(TokenIdx(idx = cur))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Not, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                ExprPrefix.Not(TokenIdx(idx = cur))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


binOp(state: ParserState[Token, ()]) BinOp / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Plus, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.Add
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Minus, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.Subtract
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Star, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.Multiply
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Slash, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.Divide
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.EqEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.Equal
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.ExclamationEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.NotEqual
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.And, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.And
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Or, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.Or
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Pipe, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.BitOr
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Amp, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.BitAnd
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RAngle, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.Gt
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DoubleRAngle, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.RightShift
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RAngleEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.GtEq
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LAngle, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.Lt
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DoubleLAngle, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.LeftShift
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LAngleEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                BinOp.LtEq
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


matchAlt[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Alt[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let pat = pat(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let guard = altGuard(state)
                    guard,
            )
            let guard = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body = Vec.empty()
            body.push(stmt(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let bodyLen0 = body.len()
                let symResult = try(\(): body.push(stmt(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        body.truncate(bodyLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Alt(pat, guard, rhs = body)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let pat = pat(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let guard = altGuard(state)
                    guard,
            )
            let guard = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body = stmt(state)
            let val = do:
                Alt(pat, guard, rhs = Vec.[body])
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


altGuard[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Expr[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.If, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let expr = expr(state)
            let val = do:
                expr
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


fnArgs[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Vec[FunArg[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let v0 = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Colon, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let ty0 = type_(state)
                    ty0,
            )
            let ty0 = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let zeroOrMoreCursor0 = state._cursor
            let vs = Vec.empty()
            loop:
                let vsLen0 = vs.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        let v = state.nextCursor()
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.LowerId, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        let optionalCursor0 = state._cursor
                        let symResult = try(
                            \():
                                if state.peek() is Option.Some(sym)
                                        and sym
                                            is Token(kind = TokenKind.Colon, ..):
                                    state._cursor += 1
                                else:
                                    throw(
                                        state.updateErrorCursor(state._cursor)
                                    )
                                let ty = type_(state)
                                ty,
                        )
                        let ty = match symResult:
                            Result.Err(err):
                                state._cursor = optionalCursor0
                                Option.None
                            Result.Ok(ok):
                                ()
                                Option.Some(ok)
                        vs.push((v = v, ty = ty)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        vs.truncate(vsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let val = do:
                let vec: Vec[FunArg[exts]] = Vec.fromIter(
                    once(FunArg(name = newId(v0), ty = ty0)).chain(
                        vs.iter().map(
                            \(v: (v: U32, ty: Option[Type[exts]])):
                                FunArg(name = newId(v.v), ty = v.ty),
                        ),
                    ),
                )
                vec
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


stmt[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Stmt[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Break, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let labelLoc = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let label = if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Label, ..):
                        state._cursor += 1
                        sym
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    label,
            )
            let label = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Stmt.Break(
                    BreakStmt(
                        label = label.map(\(l: Token): newId(labelLoc)),
                        level = 0,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Continue, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let labelLoc = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let label = if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Label, ..):
                        state._cursor += 1
                        sym
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    label,
            )
            let label = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Stmt.Continue(
                    ContinueStmt(
                        label = label.map(\(l: Token): newId(labelLoc)),
                        level = 0,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Let, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let pat = pat(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Colon, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let ty = type_(state)
                    ty,
            )
            let ty = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Eq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let rhs = letRhs(state)
            let val = do:
                Stmt.Let(
                    LetStmt(
                        lhs = pat, ty, rhs, _firstToken = TokenIdx(idx = cur)
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let label = loopLabel(state)
                    label,
            )
            let label = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.For, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let pat = pat(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Colon, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let ty = type_(state)
                    ty,
            )
            let ty = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.In, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let expr = inlineExpr(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body = Vec.empty()
            body.push(stmt(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let bodyLen0 = body.len()
                let symResult = try(\(): body.push(stmt(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        body.truncate(bodyLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Stmt.For(
                    ForStmt(
                        label,
                        pat,
                        astTy = ty,
                        expr,
                        body,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let label = loopLabel(state)
                    label,
            )
            let label = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.While, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let cond = inlineExpr(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body = Vec.empty()
            body.push(stmt(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let bodyLen0 = body.len()
                let symResult = try(\(): body.push(stmt(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        body.truncate(bodyLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Stmt.While(
                    WhileStmt(
                        label, cond, body, _firstToken = TokenIdx(idx = cur)
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let label = loopLabel(state)
                    label,
            )
            let label = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Loop, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body = Vec.empty()
            body.push(stmt(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let bodyLen0 = body.len()
                let symResult = try(\(): body.push(stmt(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        body.truncate(bodyLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Stmt.Loop(LoopStmt(body, _firstToken = TokenIdx(idx = cur)))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let lhs = inlineExpr(state)
            let rhs = stmtExprCont(state)
            let val = do:
                match rhs:
                    Option.None: Stmt.Expr(lhs)
                    Option.Some((op, rhs)):
                        Stmt.Assign(AssignStmt(lhs, rhs, op))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let expr = blockExpr(state)
            let val = do:
                Stmt.Expr(expr)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


stmtExprCont[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Option[(op: AssignOp, rhs: Expr[exts])] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Option.None
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let op = assignOp(state)
            let expr = blockExpr(state)
            let val = do:
                Option.Some((op = op, rhs = expr))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let op = assignOp(state)
            let expr = inlineExpr(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Option.Some((op = op, rhs = expr))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


loopLabel(state: ParserState[Token, ()]) Id / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let id = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Label, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                newId(id)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


letRhs[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Expr[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let expr = inlineExpr(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                expr
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let expr = blockExpr(state)
            let val = do:
                expr
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


assignOp(state: ParserState[Token, ()]) AssignOp / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Eq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                AssignOp.Eq
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.PlusEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                AssignOp.PlusEq
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.MinusEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                AssignOp.MinusEq
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.StarEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                AssignOp.StarEq
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.CaretEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                AssignOp.CaretEq
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


pat[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Pat[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let p0 = simplePat(state)
            let zeroOrMoreCursor0 = state._cursor
            let ps = Vec.empty()
            loop:
                let psLen0 = ps.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Pipe, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ps.push(simplePat(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ps.truncate(psLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let val = do:
                Pat.Or(Vec.fromIter(once(p0).chain(ps.iter())))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


simplePat[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Pat[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Tilde, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let pat = simplePat(state)
            let val = do:
                Pat.Variant(
                    VariantPat(pat, ..AstExts[exts].defaultVariantPatExts())
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let var_ = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Pat.Var(VarPat(var_ = newId(var_)))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let con = con(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.LParen, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let optionalCursor0 = state._cursor
                    let symResult = try(
                        \():
                            let pats = conFieldPats(state)
                            pats,
                    )
                    let pats = match symResult:
                        Result.Err(err):
                            state._cursor = optionalCursor0
                            Option.None
                        Result.Ok(ok):
                            ()
                            Option.Some(ok)
                    let last = state.nextCursor()
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.RParen, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let fs = (pats = pats, last = last)
                    fs,
            )
            let fs = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                Pat.Con(
                    ConPat(
                        con,
                        fields =
                            match fs:
                                Option.None: Vec.empty()
                                Option.Some((pats, ..)):
                                    pats.map(\(ps): ps.fields).unwrapOr(
                                        Vec.empty()
                                    ),
                        rest =
                            match fs:
                                Option.None: RestPat.No
                                Option.Some((pats, ..)):
                                    pats.map(\(ps): ps.rest).unwrapOr(
                                        RestPat.No
                                    ),
                        _lastToken =
                            match fs:
                                Option.None:
                                    match con.userTyArgs:
                                        Option.Some(tyArgs): tyArgs._lastToken
                                        Option.None:
                                            match con.con:
                                                Option.Some(conId): conId.token
                                                Option.None: con._firstToken
                                Option.Some((last, ..)): TokenIdx(idx = last),
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let pats = conFieldPats(state)
                    pats,
            )
            let pats = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Pat.Record(
                    RecordPat(
                        fields =
                            pats.map(\(ps): ps.fields).unwrapOr(Vec.empty()),
                        rest = pats.map(\(ps): ps.rest).unwrapOr(RestPat.No),
                        _firstToken = TokenIdx(idx = first),
                        _lastToken = TokenIdx(idx = last),
                        ..AstExts[exts].defaultRecordPatExts()
                    ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Underscore, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Pat.Ignore(TokenIdx(idx = cur))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.BeginStr, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let end = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.EndStr, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let str = end.text
                let str = str.substr(0, str.len() - 1)
                Pat.Str(str, TokenIdx(idx = cur))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let cur = state.nextCursor()
            let char = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Char, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Pat.Char(parseCharLit(char.text), TokenIdx(idx = cur))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


conFieldPats[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) (fields: Vec[Named[Pat[exts]]], rest: RestPat) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let var_ = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (
                    fields = Vec.empty(),
                    rest = RestPat.Bind(VarPat(var_ = newId(var_))),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                (fields = Vec.empty(), rest = RestPat.Ignore)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let p0 = conFieldPat(state)
            let zeroOrMoreCursor0 = state._cursor
            let ps = Vec.empty()
            loop:
                let psLen0 = ps.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ps.push(conFieldPat(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ps.truncate(psLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let rest = conFieldPatsCont(state)
                    rest,
            )
            let rest = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                let fields: Vec[Named[Pat[exts]]] = Vec.fromIter(
                    once(p0).chain(ps.iter())
                )
                (fields = fields, rest = rest.unwrapOr(RestPat.No))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


conFieldPatsCont(state: ParserState[Token, ()]) RestPat / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let var_ = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                RestPat.Bind(VarPat(var_ = newId(var_)))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                RestPat.Ignore
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                RestPat.No
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


conFieldPat[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Named[Pat[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Eq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let pat = pat(state)
            let val = do:
                Named(name = Option.Some(newId(name)), node = pat)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let pat = pat(state)
            let val = do:
                Named(name = Option.None, node = pat)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


importDecl(state: ParserState[Token, ()]) ImportDecl / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Import, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let p0 = path(state)
            let zeroOrMoreCursor0 = state._cursor
            let ps = Vec.empty()
            loop:
                let psLen0 = ps.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ps.push(path(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ps.truncate(psLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                ps.insert(0, p0)
                ImportDecl(paths = ps)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


path(state: ParserState[Token, ()]) Vec[Id] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let p0 = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            let ps = Vec.empty()
            loop:
                let psLen0 = ps.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Slash, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ps.push(state.nextCursor())
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.UpperId, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ps.truncate(psLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let val = do:
                let vec: Vec[Id] = Vec.fromIter(
                    once(newId(p0)).chain(ps.iter().map(newId))
                )
                vec
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


topFunDecl[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) FunDecl[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let prim_ = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Prim, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let sig = topFunSig(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                FunDecl(
                    prim_ = Option.Some(TokenIdx(idx = prim_)),
                    parentTy = sig.parentTy,
                    name = sig.name,
                    sig = sig.sig,
                    body = Option.None,
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let sig = topFunSig(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body = Vec.empty()
            body.push(stmt(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let bodyLen0 = body.len()
                let symResult = try(\(): body.push(stmt(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        body.truncate(bodyLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                FunDecl(
                    prim_ = Option.None,
                    parentTy = sig.parentTy,
                    name = sig.name,
                    sig = sig.sig,
                    body = Option.Some(body),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let sig = topFunSig(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let body = inlineExpr(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                FunDecl(
                    prim_ = Option.None,
                    parentTy = sig.parentTy,
                    name = sig.name,
                    sig = sig.sig,
                    body = Option.Some(Vec.[Stmt.Expr(body)]),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


topFunSig[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) (parentTy: Option[AstTyId[exts]], name: Id, sig: FunSig[exts]) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let parentTy = state.nextCursor()
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.UpperId, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Dot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    parentTy,
            )
            let parentTy = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ctx = context(state)
                    ctx,
            )
            let ctx = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let lparen = state.nextCursor()
            let params = paramList(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ret = returnTy(state)
                    ret,
            )
            let ret = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                (
                    parentTy = parentTy.map(\(id: U32): newTyId(id)),
                    name = newId(name),
                    sig =
                        FunSig(
                            context = ctx,
                            self_ = SelfParam.No,
                            params,
                            exceptions = ret.exn,
                            returnTy = ret.ret,
                            lparen = TokenIdx(idx = lparen),
                            ..AstExts[exts].defaultFunSigExts()
                        ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


context[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Context[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let p0 = pred(state)
            let zeroOrMoreCursor0 = state._cursor
            let ps = Vec.empty()
            loop:
                let psLen0 = ps.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ps.push(pred(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ps.truncate(psLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Context(
                    preds = Vec.fromIter(once(p0).chain(ps.iter())),
                    _firstToken = TokenIdx(idx = first),
                    _lastToken = TokenIdx(idx = last),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


pred[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Pred_[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let varId = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Colon, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let kind = type_(state)
                    kind,
            )
            let kind = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                Pred_.Kind(name = newId(varId), kind)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let app = namedType(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Dot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let name = state.nextCursor()
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.UpperId, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Eq, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let ty = type_(state)
                    let selection = (name = name, ty = ty)
                    selection,
            )
            let selection = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                match selection:
                    Option.None: Pred_.App(app)
                    Option.Some(selection):
                        Pred_.AssocTyEq(
                            ty = app,
                            assocTy = newId(selection.name),
                            eq = selection.ty,
                        )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


paramList[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Vec[FunArg[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Vec.empty()
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let p0 = param(state)
            let zeroOrMoreCursor0 = state._cursor
            let ps = Vec.empty()
            loop:
                let psLen0 = ps.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ps.push(param(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ps.truncate(psLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let vec: Vec[FunArg[exts]] = Vec.fromIter(
                    once(p0).chain(ps.iter())
                )
                vec
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


param[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) FunArg[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Colon, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let ty = type_(state)
                    ty,
            )
            let ty = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                FunArg(name = newId(name), ty = ty)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


traitDecl[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) TraitDecl[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Trait, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let tys = typeParams(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let rhs = traitDeclRhs(state)
                    rhs,
            )
            let rhs = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                TraitDecl(
                    name = newId(name),
                    typeParams = tys,
                    items = rhs.unwrapOr(Vec.empty()),
                    ..AstExts[exts].defaultTraitDeclExts()
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


traitDeclRhs[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Vec[TraitDeclItem[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Vec.empty()
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let items = Vec.empty()
            items.push(traitDeclItem(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let itemsLen0 = items.len()
                let symResult = try(\(): items.push(traitDeclItem(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        items.truncate(itemsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                items
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


traitDeclItem[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) TraitDeclItem[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Type, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Colon, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let kind = type_(state)
                    kind,
            )
            let kind = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Eq, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let default = type_(state)
                    default,
            )
            let default = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                TraitDeclItem.Type(name = newId(name), kind, default)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let fun = funDecl(state)
            let val = do:
                TraitDeclItem.Fun(fun)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


implDecl[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) ImplDecl[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Impl, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ctx = context(state)
                    ctx,
            )
            let ctx = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let t0 = type_(state)
            let zeroOrMoreCursor0 = state._cursor
            let ts = Vec.empty()
            loop:
                let tsLen0 = ts.len()
                let symResult = try(
                    \():
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ts.push(type_(state)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ts.truncate(tsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let rhs = implDeclRhs(state)
            let val = do:
                ImplDecl(
                    context = ctx,
                    trait_ = newTyId(name),
                    tys = Vec.fromIter(once(t0).chain(ts.iter())),
                    items = rhs,
                    _firstToken = TokenIdx(idx = first),
                    ..AstExts[exts].defaultImplDeclExts()
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


implDeclRhs[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Vec[ImplDeclItem[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Vec.empty()
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let items = Vec.empty()
            items.push(implDeclItem(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let itemsLen0 = items.len()
                let symResult = try(\(): items.push(implDeclItem(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        items.truncate(itemsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                items
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


implDeclItem[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) ImplDeclItem[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Type, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Eq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let rhs = type_(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                ImplDeclItem.Type(assocTy = newId(name), rhs,)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let fun = funDecl(state)
            let val = do:
                ImplDeclItem.Fun(fun)
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


funDecl[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) FunDecl[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let prim_ = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let primKw = if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Prim, ..):
                        state._cursor += 1
                        sym
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    primKw,
            )
            let primKw = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let sig = funSig(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                FunDecl(
                    prim_ = primKw.map(\(kw): TokenIdx(idx = prim_)),
                    parentTy = Option.None,
                    name = sig.id,
                    sig = sig.sig,
                    body = Option.None,
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            let sig = funSig(state)
            let stmts = funDeclRhs(state)
            let val = do:
                FunDecl(
                    prim_ = Option.None,
                    parentTy = Option.None,
                    name = sig.id,
                    sig = sig.sig,
                    body = Option.Some(stmts),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


funDeclRhs[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Vec[Stmt[exts]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let stmts = Vec.empty()
            stmts.push(stmt(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let stmtsLen0 = stmts.len()
                let symResult = try(\(): stmts.push(stmt(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        stmts.truncate(stmtsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                stmts
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let expr = inlineExpr(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                let vec: Vec[Stmt[exts]] = Vec.[Stmt.Expr(expr)]
                vec
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


funSig[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) (id: Id, sig: FunSig[exts]) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let id = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ctx = context(state)
                    ctx,
            )
            let ctx = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let lparen = state.nextCursor()
            let params = paramList(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                \():
                    let ret = returnTy(state)
                    ret,
            )
            let ret = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let val = do:
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                (
                    id = newId(id),
                    sig =
                        FunSig(
                            context = ctx,
                            self_ = SelfParam.No,
                            params,
                            exceptions = ret.exn,
                            returnTy = ret.ret,
                            lparen = TokenIdx(idx = lparen),
                            ..AstExts[exts].defaultFunSigExts()
                        ),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


attr[AstExts[exts], AstIds[AstExts[exts].Ids],](state: ParserState[Token, ()]) Attribute[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let open = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.HashLBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let expr = expr(state)
            let close = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Attribute(
                    expr,
                    open = TokenIdx(idx = open),
                    close = TokenIdx(idx = close),
                )
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))
