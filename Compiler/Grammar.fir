# This is generated file, do not edit.

import [
    Compiler/ParseUtils,
    Compiler/Token,
    Tool/Peg/ParseTree,
]


module(state: ParserState[Token]) Vec[TopDecl] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let zeroOrMoreCursor0 = state._cursor
            let ds = Vec.empty()
            loop:
                let dsLen0 = ds.len()
                let symResult = try(||: ds.push(topDecl(state)))
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
            let value = do:
                ds
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


topDecl(state: ParserState[Token]) TopDecl / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let t = typeDecl(state)
            let value = do:
                TopDecl.Type(t)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let t = importDecl(state)
            let value = do:
                TopDecl.Import(t)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let t = traitDecl(state)
            let value = do:
                TopDecl.Trait(t)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let t = implDecl(state)
            let value = do:
                TopDecl.Impl(t)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let t = topFunDecl(state)
            let value = do:
                TopDecl.Fun(t)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


type_(state: ParserState[Token]) Type / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let t = namedType(state)
            let value = do:
                Type.Named(t)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let id = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Type.Var(newId(id))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let t = recordType(state)
            let value = do:
                Type.Record(t)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let t = variantType(state)
            let value = do:
                Type.Variant(t)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let t = fnType(state)
            let value = do:
                Type.Fn_(t)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


namedType(state: ParserState[Token]) NamedType / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
                    ||:
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
                ||:
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
            let value = do:
                let args = Vec.fromIter(once(arg0).chain(args.iter()))
                NamedType(
                    name = newTyId(name, state._tokens),
                    args =
                        Option.Some(
                            TyArgs(
                                args,
                                _firstToken = TokenIdx(idx = argFirst),
                                _lastToken = TokenIdx(idx = argLast),
                            ),
                        ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                NamedType(
                    name = newTyId(name, state._tokens),
                    args = Option.None,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


recordType(state: ParserState[Token]) RecordType / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let start = recordTypeStart(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                RecordType(
                    fields = Vec.empty(),
                    extension = Option.None,
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let start = recordTypeStart(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let ext = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                RecordType(
                    fields = Vec.empty(),
                    extension = Option.Some(newId(ext)),
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let start = recordTypeStart(state)
            let f0 = recordTypeField(state)
            let zeroOrMoreCursor0 = state._cursor
            let fs = Vec.empty()
            loop:
                let fsLen0 = fs.len()
                let symResult = try(
                    ||:
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
                ||:
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
            let value = do:
                let fields: Vec[Named[Type]] = Vec.fromIter(
                    once(f0).chain(fs.iter()),
                )
                RecordType(
                    fields,
                    extension = ext.flatten(),
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


recordTypeStart(state: ParserState[Token]) (start: TokenIdx, isRow: Bool) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let start = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                (start = TokenIdx(idx = start), isRow = Bool.False)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let start = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParenRow, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                (start = TokenIdx(idx = start), isRow = Bool.True)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


recordTypeCont(state: ParserState[Token]) Option[Id] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.DotDot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let id = state.nextCursor()
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.LowerId, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    id,
            )
            let id = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let value = do:
                id.map(|id: U32|: newId(id))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


variantType(state: ParserState[Token]) VariantType / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let start = variantTypeStart(state)
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                VariantType(
                    alts = Vec.empty(),
                    extension = Option.None,
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let start = variantTypeStart(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let ext = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let last = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                VariantType(
                    alts = Vec.empty(),
                    extension = Option.Some(newId(ext)),
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let start = variantTypeStart(state)
            let alt0 = namedType(state)
            let zeroOrMoreCursor0 = state._cursor
            let alts = Vec.empty()
            loop:
                let altsLen0 = alts.len()
                let symResult = try(
                    ||:
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
                ||:
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
            let value = do:
                VariantType(
                    alts = Vec.fromIter(once(alt0).chain(alts.iter())),
                    extension = ext.flatten(),
                    isRow = start.isRow,
                    _firstToken = start.start,
                    _lastToken = TokenIdx(idx = last),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


variantTypeStart(state: ParserState[Token]) (start: TokenIdx, isRow: Bool) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let start = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracket, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                (start = TokenIdx(idx = start), isRow = Bool.False)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let start = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LBracketRow, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                (start = TokenIdx(idx = start), isRow = Bool.True)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


variantTypeCont(state: ParserState[Token]) Option[Id] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.DotDot, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let id = state.nextCursor()
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.LowerId, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    id,
            )
            let id = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let value = do:
                id.map(|id: U32|: newId(id))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


recordTypeFields(state: ParserState[Token]) Vec[Named[Type]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let f0 = recordTypeField(state)
            let zeroOrMoreCursor0 = state._cursor
            let fs = Vec.empty()
            loop:
                let fsLen0 = fs.len()
                let symResult = try(
                    ||:
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
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                let vec: Vec[Named[Type]] = Vec.fromIter(
                    once(f0).chain(fs.iter()),
                )
                vec
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let f0 = recordTypeField(state)
            let zeroOrMoreCursor0 = state._cursor
            let fs = Vec.empty()
            loop:
                let fsLen0 = fs.len()
                let symResult = try(
                    ||:
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
                ||:
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
            let value = do:
                let vec: Vec[Named[Type]] = Vec.fromIter(
                    once(f0).chain(fs.iter()),
                )
                vec
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


recordTypeField(state: ParserState[Token]) Named[Type] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
            let value = do:
                Named(name = Option.Some(newId(name)), node = ty)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let ty = type_(state)
            let value = do:
                Named(name = Option.None, node = ty)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


fnType(state: ParserState[Token]) FnType / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
                ||:
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
                ||:
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
            let value = do:
                let args = args.unwrapOr(Vec.empty())
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                FnType(
                    args,
                    ret = ret.ret,
                    exceptions = ret.exn,
                    _firstToken = TokenIdx(idx = first),
                    _rparen = TokenIdx(idx = rparen),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


fnArgTys(state: ParserState[Token]) Vec[Type] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let t0 = type_(state)
            let zeroOrMoreCursor0 = state._cursor
            let ts = Vec.empty()
            loop:
                let tsLen0 = ts.len()
                let symResult = try(
                    ||:
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
                ||:
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
            let value = do:
                let vec: Vec[Type] = Vec.fromIter(once(t0).chain(ts.iter()))
                vec
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


returnTy(state: ParserState[Token]) (ret: Option[Type], exn: Option[Type]) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let ret = type_(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Slash, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let exn = type_(state)
            let value = do:
                (ret = Option.Some(ret), exn = Option.Some(exn))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let ret = type_(state)
            let value = do:
                (ret = Option.Some(ret), exn = Option.None)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Slash, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let exn = type_(state)
            let value = do:
                (ret = Option.None, exn = Option.Some(exn))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


typeDecl(state: ParserState[Token]) TypeDecl / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
                ||:
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
            let rhs = Vec.empty()
            rhs.push(conDecl(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let rhsLen0 = rhs.len()
                let symResult = try(||: rhs.push(conDecl(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        rhs.truncate(rhsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                TypeDecl(
                    prim_ = Option.None,
                    name = newId(name),
                    typeParams =
                        match params:
                            Option.Some(params): params
                            Option.None: Vec.empty(),
                    typeParamKinds = Vec.empty(),
                    rhs = Option.Some(TypeDeclRhs.Sum(rhs)),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
                ||:
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
                ||:
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
            let value = do:
                let fs = match fs:
                    Option.Some(fs): fs.fields
                    Option.None: ConFields.Empty
                TypeDecl(
                    prim_ = Option.None,
                    name = newId(name),
                    typeParams =
                        match params:
                            Option.Some(params): params
                            Option.None: Vec.empty(),
                    typeParamKinds = Vec.empty(),
                    rhs = Option.Some(TypeDeclRhs.Product(fs)),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
                ||:
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
            let value = do:
                TypeDecl(
                    prim_ = Option.Some(TokenIdx(idx = prim_)),
                    name = newId(name),
                    typeParams =
                        match params:
                            Option.Some(params): params
                            Option.None: Vec.empty(),
                    typeParamKinds = Vec.empty(),
                    rhs = Option.None,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


typeParams(state: ParserState[Token]) Vec[Id] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let id0 = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            let ids = Vec.empty()
            loop:
                let idsLen0 = ids.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        ids.push(state.nextCursor())
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.LowerId, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        ids.truncate(idsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                let vec: Vec[Id] = Vec.fromIter(
                    once(newId(id0)).chain(ids.iter().map(|id: U32|: newId(id))),
                )
                vec
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


conDecl(state: ParserState[Token]) ConDecl / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                let name = newId(name)
                match fs:
                    Option.Some(fs):
                        ConDecl(
                            name,
                            fields = fs.fields,
                            _lastToken = fs.lastToken,
                        )
                    Option.None:
                        ConDecl(
                            name,
                            fields = ConFields.Empty,
                            _lastToken = name.token,
                        )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


conFields(state: ParserState[Token]) (fields: ConFields, lastToken: TokenIdx) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
            let value = do:
                (fields = ConFields.Empty, lastToken = TokenIdx(idx = last))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
                    ||:
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
                ||:
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
                    and sym is Token(kind = TokenKind.RParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                let vec: Vec[(name: Option[Id], ty: Type)] = Vec.fromIter(
                    once(f0).chain(fs.iter()),
                )
                (fields = processFields(vec), lastToken = TokenIdx(idx = last))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


conField(state: ParserState[Token]) (name: Option[Id], ty: Type) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                (name = name.map(|name: U32|: newId(name)), ty = ty)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


expr(state: ParserState[Token]) Expr / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let e = inlineExpr(state)
            let value = do:
                e
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let e = blockExpr(state)
            let value = do:
                e
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


inlineExpr(state: ParserState[Token]) Expr / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let expr = prefixExpr(state)
            let zeroOrMoreCursor0 = state._cursor
            let cont = Vec.empty()
            loop:
                let contLen0 = cont.len()
                let symResult = try(||: cont.push(inlineExprCont(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        cont.truncate(contLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let value = do:
                associate(expr, cont)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


blockExpr(state: ParserState[Token]) Expr / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
                let symResult = try(||: alts.push(matchAlt(state)))
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
            let value = do:
                Expr.Match(
                    MatchExpr(
                        scrutinee = scrut,
                        alts,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
                let symResult = try(||: body0.push(stmt(state)))
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
                    ||:
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
                            let symResult = try(||: body.push(stmt(state)))
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
                ||:
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
                        let symResult = try(||: else_.push(stmt(state)))
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
            let value = do:
                Expr.If(
                    IfExpr(
                        _firstToken = TokenIdx(idx = cur),
                        branches =
                            Vec.fromIter(
                                once(IfBranch(guard = cond0, body = body0))
                                    .chain(
                                    conds.iter().map(
                                        |branch: (cond: Expr, body: Vec[Stmt])|:
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
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
                let symResult = try(||: body.push(stmt(state)))
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
            let value = do:
                Expr.Do(DoExpr(body, _firstToken = TokenIdx(idx = cur)))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.PipePipe, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                let symResult = try(||: body.push(stmt(state)))
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
            let value = do:
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                Expr.Fn_(
                    FnExpr(
                        sig =
                            FunSig(
                                typeParams = Vec.empty(),
                                context = Option.None,
                                self_ = SelfParam.No,
                                params = Vec.empty(),
                                exceptions = ret.exn,
                                returnTy = ret.ret,
                            ),
                        body,
                        idx = 0,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Pipe, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                    and sym is Token(kind = TokenKind.Pipe, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                let symResult = try(||: body.push(stmt(state)))
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
            let value = do:
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                Expr.Fn_(
                    FnExpr(
                        sig =
                            FunSig(
                                typeParams = Vec.empty(),
                                context = Option.None,
                                self_ = SelfParam.No,
                                params = args.unwrapOr(Vec.empty()),
                                exceptions = ret.exn,
                                returnTy = ret.ret,
                            ),
                        body,
                        idx = 0,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


inlineExprCont(state: ParserState[Token]) InlineExprCont / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let op = binOp(state)
            let rhs = prefixExpr(state)
            let value = do:
                InlineExprCont.BinOp(op, rhs)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Is, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let pat = pat(state)
            let value = do:
                InlineExprCont.Is(pat)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


prefixExpr(state: ParserState[Token]) Expr / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                let symResult = try(||: suffix.push(exprSuffix(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        suffix.truncate(suffixLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let value = do:
                let ret = expr
                for suffix_ in suffix.iter():
                    match suffix_:
                        ExprSuffix.Field(field, tyArgs):
                            ret = Expr.FieldSelect(
                                FieldSelectExpr(
                                    object = ret,
                                    field,
                                    userTyArgs = tyArgs,
                                ),
                            )
                        ExprSuffix.Args(args, _lastToken):
                            ret = Expr.Call(
                                CallExpr(fun = ret, args, _lastToken),
                            )
                if pfx is Option.Some(pfx):
                    match pfx:
                        ExprPrefix.Tilde(token): ()
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
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


exprSuffix(state: ParserState[Token]) ExprSuffix / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let field = field(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                ExprSuffix.Field(field, tyArgs = args)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let args = args(state)
            let value = do:
                ExprSuffix.Args(
                    args = args.args,
                    _lastToken = TokenIdx(idx = args.cursorRight),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


field(state: ParserState[Token]) Id / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
            let value = do:
                newId(field)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


args(state: ParserState[Token]) (args: Vec[Named[Expr]], cursorRight: U32) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    let arg0 = arg(state)
                    let zeroOrMoreCursor0 = state._cursor
                    let args = Vec.empty()
                    loop:
                        let argsLen0 = args.len()
                        let symResult = try(
                            ||:
                                if state.peek() is Option.Some(sym)
                                        and sym
                                            is Token(kind = TokenKind.Comma, ..):
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
                    let optionalCursor0 = state._cursor
                    let symResult = try(
                        ||:
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
            let value = do:
                (
                    args =
                        match args:
                            Option.None: Vec.empty()
                            Option.Some((arg0, args)):
                                let vec: Vec[Named[Expr]] = Vec.fromIter(
                                    once(arg0).chain(args.iter()),
                                )
                                vec,
                    cursorRight = last,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


arg(state: ParserState[Token]) Named[Expr] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
            let value = do:
                Named(name = Option.Some(newId(name)), node = expr)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let expr = expr(state)
            let value = do:
                Named(name = Option.None, node = expr)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


simpleExpr(state: ParserState[Token]) Expr / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let seq = sequence(state)
            let value = do:
                seq
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let var_ = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                Expr.Var(
                    VarExpr(
                        id = newVarId(var_, state._tokens),
                        userTyArgs = tyArgs,
                        tyArgs = Vec.empty(),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let con = constructor(state)
            let value = do:
                Expr.ConstrSelect(con)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    let e0 = parenExpr(state)
                    let zeroOrMoreCursor0 = state._cursor
                    let es = Vec.empty()
                    loop:
                        let esLen0 = es.len()
                        let symResult = try(
                            ||:
                                if state.peek() is Option.Some(sym)
                                        and sym
                                            is Token(kind = TokenKind.Comma, ..):
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
                    let optionalCursor0 = state._cursor
                    let symResult = try(
                        ||:
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
            let value = do:
                match exprs:
                    Option.None:
                        Expr.Record(
                            RecordExpr(
                                fields = Vec.empty(),
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
                                                fields.es.iter(),
                                            ),
                                        ),
                                    _firstToken = TokenIdx(idx = first),
                                    _lastToken = TokenIdx(idx = last),
                                ),
                            )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Return, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                Expr.Return(ReturnExpr(expr, _firstToken = TokenIdx(idx = cur)))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.PipePipe, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                Expr.Fn_(
                    FnExpr(
                        sig =
                            FunSig(
                                typeParams = Vec.empty(),
                                context = Option.None,
                                self_ = SelfParam.No,
                                params = Vec.empty(),
                                exceptions = ret.exn,
                                returnTy = ret.ret,
                            ),
                        body = Vec.[Stmt.Expr(body)],
                        idx = 0,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Pipe, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                    and sym is Token(kind = TokenKind.Pipe, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                Expr.Fn_(
                    FnExpr(
                        sig =
                            FunSig(
                                typeParams = Vec.empty(),
                                context = Option.None,
                                self_ = SelfParam.No,
                                params = args.unwrapOr(Vec.empty()),
                                exceptions = ret.exn,
                                returnTy = ret.ret,
                            ),
                        body = Vec.[Stmt.Expr(body)],
                        idx = 0,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            let int = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Int, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
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
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            let int = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.HexInt, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                let text = int.text
                if not text.startsWith("0x"):
                    panic("Bug in int lexer")
                let text = text.substr(2, text.len())
                let intStr = StrBuf.withCapacity(text.len())
                for char: Char in text.chars():
                    if char == '_':
                        continue
                    intStr.push(char)
                Expr.Int(
                    IntExpr(
                        text = intStr.toStr(),
                        suffix = Option.None,
                        radix = 16,
                        parsed = 0,
                        token = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            let int = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.BinInt, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                let text = int.text
                if not text.startsWith("0b"):
                    panic("Bug in int lexer")
                let text = text.substr(2, text.len())
                let intStr = StrBuf.withCapacity(text.len())
                for char: Char in text.chars():
                    if char == '_':
                        continue
                    intStr.push(char)
                Expr.Int(
                    IntExpr(
                        text = intStr.toStr(),
                        suffix = Option.None,
                        radix = 2,
                        parsed = 0,
                        token = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            let str = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Str, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Expr.Str(
                    StrExpr(
                        parts = parseStrParts(str.text),
                        token = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            let char = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Char, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Expr.Char(
                    CharExpr(
                        char = parseCharLit(char.text),
                        token = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


sequence(state: ParserState[Token]) Expr / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                Expr.Seq(
                    SeqExpr(
                        ty,
                        elems = elems.elems,
                        _lbracket = elems.lbracket,
                        _rbracket = elems.rbracket,
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


seqElems(state: ParserState[Token]) (elems: Vec[SeqElem], lbracket: TokenIdx, rbracket: TokenIdx) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
            let value = do:
                (
                    elems = Vec.empty(),
                    lbracket = TokenIdx(idx = lbracket),
                    rbracket = TokenIdx(idx = rbracket),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
                    ||:
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
                ||:
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
            let value = do:
                let vec: Vec[SeqElem] = Vec.fromIter(once(e0).chain(es.iter()))
                (
                    elems = vec,
                    lbracket = TokenIdx(idx = lbracket),
                    rbracket = TokenIdx(idx = rbracket),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


seqElem(state: ParserState[Token]) SeqElem / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let e1 = inlineExpr(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                match e2:
                    Option.None: SeqElem(key = Option.None, value = e1)
                    Option.Some((e = e2)):
                        SeqElem(key = Option.Some(e1), value = e2)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


constructor(state: ParserState[Token]) Constructor / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let ty = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.UpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                ||:
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
            let value = do:
                Constructor(
                    variant = Bool.False,
                    ty = newTyId(ty, state._tokens),
                    constr = con.map(|con: U32|: newId(con)),
                    userTyArgs,
                    tyArgs = Vec.empty(),
                    _firstToken = TokenIdx(idx = ty),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let ty = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.TildeUpperId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                ||:
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
            let value = do:
                Constructor(
                    variant = Bool.True,
                    ty = newTyId(ty, state._tokens),
                    constr = con.map(|con: U32|: newId(con)),
                    userTyArgs,
                    tyArgs = Vec.empty(),
                    _firstToken = TokenIdx(idx = ty),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


tyArgs(state: ParserState[Token]) TyArgs / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
                    ||:
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
                ||:
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
            let value = do:
                let ts: Vec[Type] = Vec.fromIter(once(t0).chain(ts.iter()))
                TyArgs(
                    args = ts,
                    _firstToken = TokenIdx(idx = first),
                    _lastToken = TokenIdx(idx = last),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


parenExpr(state: ParserState[Token]) Named[Expr] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
            let value = do:
                Named(name = Option.Some(newId(name)), node = expr)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let expr = expr(state)
            let value = do:
                Named(name = Option.None, node = expr)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


exprPrefix(state: ParserState[Token]) ExprPrefix / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Tilde, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ExprPrefix.Tilde(TokenIdx(idx = cur))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Minus, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ExprPrefix.Minus(TokenIdx(idx = cur))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Not, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ExprPrefix.Not(TokenIdx(idx = cur))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


binOp(state: ParserState[Token]) BinOp / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Plus, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.Add
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Minus, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.Subtract
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Star, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.Multiply
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Slash, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.Divide
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.EqEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.Equal
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.ExclamationEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.NotEqual
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.And, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.And
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Or, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.Or
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Pipe, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.BitOr
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Amp, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.BitAnd
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RAngle, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.Gt
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DoubleRAngle, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.RightShift
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.RAngleEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.GtEq
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LAngle, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.Lt
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DoubleLAngle, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.LeftShift
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LAngleEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                BinOp.LtEq
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


matchAlt(state: ParserState[Token]) Alt / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let pattern = pat(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                let symResult = try(||: body.push(stmt(state)))
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
            let value = do:
                Alt(pattern, guard, rhs = body)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let pattern = pat(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                Alt(pattern, guard, rhs = Vec.[body])
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


altGuard(state: ParserState[Token]) Expr / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.If, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let expr = expr(state)
            let value = do:
                expr
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


fnArgs(state: ParserState[Token]) Vec[FunArg] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let v0 = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                    ||:
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
                            ||:
                                if state.peek() is Option.Some(sym)
                                        and sym
                                            is Token(kind = TokenKind.Colon, ..):
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
                ||:
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
            let value = do:
                let vec: Vec[FunArg] = Vec.fromIter(
                    once(FunArg(name = newId(v0), ty = ty0)).chain(
                        vs.iter().map(
                            |v: (v: U32, ty: Option[Type])|:
                                FunArg(name = newId(v.v), ty = v.ty),
                        ),
                    ),
                )
                vec
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


stmt(state: ParserState[Token]) Stmt / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Break, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let labelLoc = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                Stmt.Break(
                    BreakStmt(
                        label = label.map(|l: Token|: newId(labelLoc)),
                        level = 0,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Continue, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let labelLoc = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                Stmt.Continue(
                    ContinueStmt(
                        label = label.map(|l: Token|: newId(labelLoc)),
                        level = 0,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Let, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let pat = pat(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                Stmt.Let(
                    LetStmt(
                        lhs = pat,
                        ty,
                        rhs,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                ||:
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
                let symResult = try(||: body.push(stmt(state)))
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
            let value = do:
                Stmt.For(
                    ForStmt(
                        label,
                        pat,
                        astTy = ty,
                        tcTy = Option.None,
                        expr,
                        exprTy = Option.None,
                        body,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                let symResult = try(||: body.push(stmt(state)))
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
            let value = do:
                Stmt.While(
                    WhileStmt(
                        label,
                        cond,
                        body,
                        _firstToken = TokenIdx(idx = cur),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                let symResult = try(||: body.push(stmt(state)))
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
            let value = do:
                Stmt.Loop(LoopStmt(body, _firstToken = TokenIdx(idx = cur)))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let lhs = inlineExpr(state)
            let rhs = stmtExprCont(state)
            let value = do:
                match rhs:
                    Option.None: Stmt.Expr(lhs)
                    Option.Some((op, rhs)):
                        Stmt.Assign(AssignStmt(lhs, rhs, op))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let expr = blockExpr(state)
            let value = do:
                Stmt.Expr(expr)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


stmtExprCont(state: ParserState[Token]) Option[(op: AssignOp, rhs: Expr)] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Option.None
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let op = assignOp(state)
            let expr = blockExpr(state)
            let value = do:
                Option.Some((op = op, rhs = expr))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let op = assignOp(state)
            let expr = inlineExpr(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Option.Some((op = op, rhs = expr))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


loopLabel(state: ParserState[Token]) Id / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let id = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Label, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                newId(id)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


letRhs(state: ParserState[Token]) Expr / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let expr = inlineExpr(state)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                expr
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let expr = blockExpr(state)
            let value = do:
                expr
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


assignOp(state: ParserState[Token]) AssignOp / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Eq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                AssignOp.Eq
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.PlusEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                AssignOp.PlusEq
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.MinusEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                AssignOp.MinusEq
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.StarEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                AssignOp.StarEq
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.CaretEq, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                AssignOp.CaretEq
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


pat(state: ParserState[Token]) Pat / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let p0 = simplePat(state)
            let zeroOrMoreCursor0 = state._cursor
            let ps = Vec.empty()
            loop:
                let psLen0 = ps.len()
                let symResult = try(
                    ||:
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
            let value = do:
                Pat.Or(Vec.fromIter(once(p0).chain(ps.iter())))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


simplePat(state: ParserState[Token]) Pat / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let var_ = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Pat.Var(VarPat(var_ = newId(var_), ty = Option.None))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let con = constructor(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.LParen, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let optionalCursor0 = state._cursor
                    let symResult = try(
                        ||:
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
            let value = do:
                Pat.Constr(
                    ConstrPat(
                        constr = con,
                        fields =
                            match fs:
                                Option.None: Vec.empty()
                                Option.Some((pats, ..)):
                                    pats.map(|ps|: ps.fields).unwrapOr(
                                        Vec.empty(),
                                    ),
                        ignoreRest =
                            match fs:
                                Option.None: Bool.False
                                Option.Some((pats, ..)):
                                    pats.map(|ps|: ps.ignoreRest).unwrapOr(
                                        Bool.False,
                                    ),
                        _lastToken =
                            match fs:
                                Option.None: con.lastToken()
                                Option.Some((last, ..)): TokenIdx(idx = last),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LParen, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                Pat.Record(
                    RecordPat(
                        fields = pats.map(|ps|: ps.fields).unwrapOr(Vec.empty()),
                        ignoreRest =
                            pats.map(|ps|: ps.ignoreRest).unwrapOr(Bool.False),
                        inferredTy = Option.None,
                        _firstToken = TokenIdx(idx = first),
                        _lastToken = TokenIdx(idx = last),
                    ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Underscore, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Pat.Ignore(TokenIdx(idx = cur))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            let str = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Str, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Pat.Str(str.text, TokenIdx(idx = cur))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let cur = state.nextCursor()
            let char = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Char, ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Pat.Char(parseCharLit(char.text), TokenIdx(idx = cur))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


conFieldPats(state: ParserState[Token]) (fields: Vec[Named[Pat]], ignoreRest: Bool) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.DotDot, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                (fields = Vec.empty(), ignoreRest = Bool.True)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let p0 = conFieldPat(state)
            let zeroOrMoreCursor0 = state._cursor
            let ps = Vec.empty()
            loop:
                let psLen0 = ps.len()
                let symResult = try(
                    ||:
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
                ||:
                    let ignoreRest = conFieldPatsCont(state)
                    ignoreRest,
            )
            let ignoreRest = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let value = do:
                let fields: Vec[Named[Pat]] = Vec.fromIter(
                    once(p0).chain(ps.iter()),
                )
                (fields = fields, ignoreRest = ignoreRest.unwrapOr(Bool.False))
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


conFieldPatsCont(state: ParserState[Token]) Bool / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
            let value = do:
                Bool.True
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Bool.False
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


conFieldPat(state: ParserState[Token]) Named[Pat] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
            let value = do:
                Named(name = Option.Some(newId(name)), node = pat)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let pat = pat(state)
            let value = do:
                Named(name = Option.None, node = pat)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


importDecl(state: ParserState[Token]) ImportDecl / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
                    ||:
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
                ||:
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
            let value = do:
                ps.insert(0, p0)
                ImportDecl(paths = ps)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


path(state: ParserState[Token]) Vec[Id] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
                    ||:
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
            let value = do:
                let vec: Vec[Id] = Vec.fromIter(
                    once(newId(p0)).chain(ps.iter().map(newId)),
                )
                vec
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


topFunDecl(state: ParserState[Token]) FunDecl / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
            let value = do:
                FunDecl(
                    prim_ = Option.Some(TokenIdx(idx = prim_)),
                    parentTy = sig.parentTy,
                    name = sig.name,
                    sig = sig.sig,
                    body = Option.None,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
                let symResult = try(||: body.push(stmt(state)))
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
            let value = do:
                FunDecl(
                    prim_ = Option.None,
                    parentTy = sig.parentTy,
                    name = sig.name,
                    sig = sig.sig,
                    body = Option.Some(body),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
            let value = do:
                FunDecl(
                    prim_ = Option.None,
                    parentTy = sig.parentTy,
                    name = sig.name,
                    sig = sig.sig,
                    body = Option.Some(Vec.[Stmt.Expr(body)]),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


topFunSig(state: ParserState[Token]) (parentTy: Option[TyId], name: Id, sig: FunSig) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                ||:
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
            let params = paramList(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                (
                    parentTy =
                        parentTy.map(|id: U32|: newTyId(id, state._tokens)),
                    name = newId(name),
                    sig =
                        FunSig(
                            typeParams = Vec.empty(),
                            context = ctx,
                            self_ = SelfParam.No,
                            params,
                            exceptions = ret.exn,
                            returnTy = ret.ret,
                        ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


parentTy(state: ParserState[Token]) Id / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let id = state.nextCursor()
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
            let value = do:
                newId(id)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


context(state: ParserState[Token]) Context / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
                    ||:
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
                ||:
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
            let value = do:
                Context(
                    preds = Vec.fromIter(once(t0).chain(ts.iter())),
                    _firstToken = TokenIdx(idx = first),
                    _lastToken = TokenIdx(idx = last),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


paramList(state: ParserState[Token]) Vec[FunArg] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
            let value = do:
                Vec.empty()
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
                    ||:
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
                ||:
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
            let value = do:
                let vec: Vec[FunArg] = Vec.fromIter(once(p0).chain(ps.iter()))
                vec
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


param(state: ParserState[Token]) FunArg / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let name = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                FunArg(name = newId(name), ty = ty)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


traitDecl(state: ParserState[Token]) TraitDecl / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
                ||:
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
            let value = do:
                TraitDecl(
                    name = newId(name),
                    typeParams = tys,
                    typeParamKinds = Vec.empty(),
                    items = rhs.unwrapOr(Vec.empty()),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


traitDeclRhs(state: ParserState[Token]) Vec[FunDecl] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Vec.empty()
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
            let fs = Vec.empty()
            fs.push(funDecl(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let fsLen0 = fs.len()
                let symResult = try(||: fs.push(funDecl(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        fs.truncate(fsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                fs
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


implDecl(state: ParserState[Token]) ImplDecl / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let first = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Impl, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
                    ||:
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
                ||:
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
            let value = do:
                ImplDecl(
                    typeParams = Vec.empty(),
                    context = ctx,
                    trait_ = newTyId(name, state._tokens),
                    tys = Vec.fromIter(once(t0).chain(ts.iter())),
                    items = rhs,
                    _firstToken = TokenIdx(idx = first),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


implDeclRhs(state: ParserState[Token]) Vec[FunDecl] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Vec.empty()
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
            let funs = Vec.empty()
            funs.push(funDecl(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let funsLen0 = funs.len()
                let symResult = try(||: funs.push(funDecl(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        funs.truncate(funsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                funs
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


funDecl(state: ParserState[Token]) FunDecl / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let prim_ = state.nextCursor()
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                FunDecl(
                    prim_ = primKw.map(|kw|: TokenIdx(idx = prim_)),
                    parentTy = Option.None,
                    name = sig.id,
                    sig = sig.sig,
                    body = Option.None,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let sig = funSig(state)
            let stmts = funDeclRhs(state)
            let value = do:
                FunDecl(
                    prim_ = Option.None,
                    parentTy = Option.None,
                    name = sig.id,
                    sig = sig.sig,
                    body = Option.Some(stmts),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


funDeclRhs(state: ParserState[Token]) Vec[Stmt] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
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
                let symResult = try(||: stmts.push(stmt(state)))
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
            let value = do:
                stmts
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
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
            let value = do:
                let vec: Vec[Stmt] = Vec.[Stmt.Expr(expr)]
                vec
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


funSig(state: ParserState[Token]) (id: Id, sig: FunSig) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let id = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let params = paramList(state)
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
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
            let value = do:
                let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
                (
                    id = newId(id),
                    sig =
                        FunSig(
                            typeParams = Vec.empty(),
                            context = ctx,
                            self_ = SelfParam.No,
                            params,
                            exceptions = ret.exn,
                            returnTy = ret.ret,
                        ),
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))
