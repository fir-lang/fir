# This is generated file, do not edit.

import Peg.ParseTree
import Token

type NonTerminal:
    RecordTypeCont
    UpperIdPath

impl ToStr[NonTerminal]:
    toStr(self: NonTerminal) Str:
        match self:
            NonTerminal.RecordTypeCont: "RecordTypeCont"
            NonTerminal.UpperIdPath: "UpperIdPath"

impl Eq[NonTerminal]:
    __eq(self: NonTerminal, other: NonTerminal) Bool:
        match (left = self, right = other):
            (left = NonTerminal.RecordTypeCont, right = NonTerminal.RecordTypeCont): Bool.True
            (left = NonTerminal.UpperIdPath, right = NonTerminal.UpperIdPath): Bool.True
            _: Bool.False

module(tokens: Vec[Token], cursor: U32) (tree: Vec[TopDecl], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let ds = Vec.empty()
        let nonTerminalResult = topDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let ds = nonTerminalResult.tree
        let ds = Vec.empty()
        loop:
            let symResult = try(||:
                let nonTerminalResult = topDecl(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                ds.push(nonTerminalResult.tree)
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if cursor == tokens.len():
            cursor
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ds
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

topDecl(tokens: Vec[Token], cursor: U32) (tree: TopDecl, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = typeDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t = nonTerminalResult.tree
        let value = do:
            TopDecl.Type(t)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = importDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t = nonTerminalResult.tree
        let value = do:
            TopDecl.Import(t)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = traitDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t = nonTerminalResult.tree
        let value = do:
            TopDecl.Trait(t)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = implDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t = nonTerminalResult.tree
        let value = do:
            TopDecl.Impl(t)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = topFunDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t = nonTerminalResult.tree
        let value = do:
            TopDecl.Fun(t)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

type_(tokens: Vec[Token], cursor: U32) (tree: Type, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = namedType(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t = nonTerminalResult.tree
        let value = do:
            Type.Named(t)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let id = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Type.Var(newId(id.text))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = recordType(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t = nonTerminalResult.tree
        let value = do:
            Type.Record(t)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = variantType(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t = nonTerminalResult.tree
        let value = do:
            Type.Variant(t)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = fnType(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t = nonTerminalResult.tree
        let value = do:
            Type.Fn_(t)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

namedType(tokens: Vec[Token], cursor: U32) (tree: NamedType, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let arg0 = nonTerminalResult.tree
        let args = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = type_(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let t = nonTerminalResult.tree
                args.push((t = t))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            let args = once(arg0).chain(args.iter().map(|arg: (t: Type)|: arg.t)).toVec()
            NamedType(name = newId(name.text), args = args)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            NamedType(name = newId(name.text), args = Vec.empty())
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordType(tokens: Vec[Token], cursor: U32) (tree: RecordType, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = recordTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let isRow = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            RecordType(fields = Vec.empty(), extension = Option.None, isRow = isRow)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = recordTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let isRow = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let ext = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            RecordType(fields = Vec.empty(), extension = Option.Some(newId(ext.text)), isRow = isRow)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = recordTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let isRow = nonTerminalResult.tree
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let f0 = nonTerminalResult.tree
        let fs = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = recordTypeField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let f = nonTerminalResult.tree
                fs.push((f = f))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            let nonTerminalResult = recordTypeCont(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let ext = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = ext)
        )
        let ext = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordTypeStart(tokens: Vec[Token], cursor: U32) (tree: Bool, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Bool.False
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParenRow, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Bool.True
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordTypeCont(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordTypeCont, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

variantType(tokens: Vec[Token], cursor: U32) (tree: VariantType, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = variantTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let isRow = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            VariantType(alts = Vec.empty(), extension = Option.None, isRow = isRow)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = variantTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let isRow = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let ext = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            VariantType(alts = Vec.empty(), extension = Option.Some(newId(ext.text)), isRow = isRow)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = variantTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let isRow = nonTerminalResult.tree
        let nonTerminalResult = variantAlt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let alt0 = nonTerminalResult.tree
        let alts = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = variantAlt(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let a = nonTerminalResult.tree
                alts.push((a = a))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            let nonTerminalResult = variantTypeCont(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let ext = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = ext)
        )
        let ext = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            VariantType(
                alts = once(alt0).chain(alts.iter().map(|alt: (a: VariantAlt)|: alt.a)).toVec(),
                extension = ext.flatten(),
                isRow = isRow,
            )
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

variantTypeStart(tokens: Vec[Token], cursor: U32) (tree: Bool, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Bool.False
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracketRow, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Bool.True
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

variantTypeCont(tokens: Vec[Token], cursor: U32) (tree: Option[Id], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let id = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
                let sym = tokens.get(cursor)
                cursor += 1
                sym
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let id = (id = id)
            (cursor = cursor, err = curErr, val = id)
        )
        let id = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        let value = do:
            id.map(|id: (id: Token)|: newId(id.id.text))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

variantAlt(tokens: Vec[Token], cursor: U32) (tree: VariantAlt, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let con = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = recordTypeFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let fields = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            VariantAlt(con = newId(con.text), fields = fields)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let con = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            VariantAlt(con = newId(con.text), fields = Vec.empty())
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordTypeFields(tokens: Vec[Token], cursor: U32) (tree: Vec[Named[Type]], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let f0 = nonTerminalResult.tree
        let fs = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = recordTypeField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let f = nonTerminalResult.tree
                fs.push((f = f))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            let vec: Vec[Named[Type]] = once(f0).chain(fs.iter().map(|f: (f: Named[Type])|: f.f)).toVec()
            vec
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let f0 = nonTerminalResult.tree
        let fs = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = recordTypeField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let f = nonTerminalResult.tree
                fs.push((f = f))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            let vec: Vec[Named[Type]] = once(f0).chain(fs.iter().map(|f: (f: Named[Type])|: f.f)).toVec()
            vec
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordTypeField(tokens: Vec[Token], cursor: U32) (tree: Named[Type], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let ty = nonTerminalResult.tree
        let value = do:
            Named(name = Option.Some(newId(name.text)), node = ty)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let ty = nonTerminalResult.tree
        let value = do:
            Named(name = Option.None, node = ty)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

fnType(tokens: Vec[Token], cursor: U32) (tree: FnType, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperFn, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let nonTerminalResult = fnArgTys(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let args = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = args)
        )
        let args = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let nonTerminalResult = returnTy(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let ret = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = ret)
        )
        let ret = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        let value = do:
            let args = args.unwrapOr(Vec.empty())
            let ret = ret.unwrapOr((ret = Option.None, exn = Option.None))
            FnType(args = args, ret = ret.ret, exceptions = ret.exn)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

fnArgTys(tokens: Vec[Token], cursor: U32) (tree: Vec[Type], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t0 = nonTerminalResult.tree
        let ts = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = type_(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let t = nonTerminalResult.tree
                ts.push((t = t))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            let vec: Vec[Type] = once(t0).chain(ts.iter().map(|t: (t: Type)|: t.t)).toVec()
            vec
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

returnTy(tokens: Vec[Token], cursor: U32) (tree: (ret: Option[Type], exn: Option[Type]), newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let ret = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Slash, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let exn = nonTerminalResult.tree
        let value = do:
            (ret = Option.Some(ret), exn = Option.Some(exn))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let ret = nonTerminalResult.tree
        let value = do:
            (ret = Option.Some(ret), exn = Option.None)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Slash, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let exn = nonTerminalResult.tree
        let value = do:
            (ret = Option.None, exn = Option.Some(exn))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

typeDecl(tokens: Vec[Token], cursor: U32) (tree: TypeDecl, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Type, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let params = nonTerminalResult.tree
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let params = (params = params)
            (cursor = cursor, err = curErr, val = params)
        )
        let params = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = typeDeclRhs(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let rhs = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            TypeDecl(
                name = newId(name.text),
                typeParams = match params:
                    Option.Some(params): params.params
                    Option.None: Vec.empty(),
                typeParamKinds = Vec.empty(),
                rhs = Option.Some(rhs),
            )
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Type, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let params = nonTerminalResult.tree
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let params = (params = params)
            (cursor = cursor, err = curErr, val = params)
        )
        let params = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            TypeDecl(
                name = newId(name.text),
                typeParams = match params:
                    Option.Some(params): params.params
                    Option.None: Vec.empty(),
                typeParamKinds = Vec.empty(),
                rhs = Option.None,
            )
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Prim, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Type, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let params = nonTerminalResult.tree
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let params = (params = params)
            (cursor = cursor, err = curErr, val = params)
        )
        let params = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            TypeDecl(
                name = newId(name.text),
                typeParams = match params:
                    Option.Some(params): params.params
                    Option.None: Vec.empty(),
                typeParamKinds = Vec.empty(),
                rhs = Option.None,
            )
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

typeParams(tokens: Vec[Token], cursor: U32) (tree: Vec[Id], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let id0 = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let ids = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let id = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
                    let sym = tokens.get(cursor)
                    cursor += 1
                    sym
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                ids.push((id = id))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            let vec: Vec[Id] =
                once(newId(id0.text)).chain(ids.iter().map(|id: (id: Token)|: newId(id.id.text))).toVec()
            vec
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

typeDeclRhs(tokens: Vec[Token], cursor: U32) (tree: TypeDeclRhs, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let cs = Vec.empty()
        let nonTerminalResult = conDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let cs = nonTerminalResult.tree
        let cs = Vec.empty()
        loop:
            let symResult = try(||:
                let nonTerminalResult = conDecl(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                cs.push(nonTerminalResult.tree)
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            TypeDeclRhs.Sum(cs)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let fs = Vec.empty()
        let nonTerminalResult = namedField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let fs = nonTerminalResult.tree
        let fs = Vec.empty()
        loop:
            let symResult = try(||:
                let nonTerminalResult = namedField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                fs.push(nonTerminalResult.tree)
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            TypeDeclRhs.Product(ConFields.Named(fs))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

conDecl(tokens: Vec[Token], cursor: U32) (tree: ConDecl, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = namedFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let fs = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ConDecl(name = newId(name.text), fields = ConFields.Named(fs))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let nonTerminalResult = unnamedFields(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let fs = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = fs)
        )
        let fs = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ConDecl(name = newId(name.text), fields = ConFields.Unnamed(fs.unwrapOr(Vec.empty())))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ConDecl(name = newId(name.text), fields = ConFields.Empty)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

namedFields(tokens: Vec[Token], cursor: U32) (tree: Vec[(name: Id, ty: Type)], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let fs = Vec.empty()
        let nonTerminalResult = namedField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let fs = nonTerminalResult.tree
        let fs = Vec.empty()
        loop:
            let symResult = try(||:
                let nonTerminalResult = namedField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                fs.push(nonTerminalResult.tree)
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            fs
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

namedField(tokens: Vec[Token], cursor: U32) (tree: (name: Id, ty: Type), newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let ty = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            (name = newId(name.text), ty = ty)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

unnamedFields(tokens: Vec[Token], cursor: U32) (tree: Vec[Type], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t0 = nonTerminalResult.tree
        let ts = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = type_(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let t = nonTerminalResult.tree
                ts.push((t = t))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            let vec: Vec[Type] = once(t0).chain(ts.iter().map(|t: (t: Type)|: t.t)).toVec()
            vec
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

expr(tokens: Vec[Token], cursor: U32) (tree: Expr, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let e = nonTerminalResult.tree
        let value = do:
            e
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

inlineExpr(tokens: Vec[Token], cursor: U32) (tree: Expr, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

upperIdPath(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dot, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.UpperIdPath, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.TildeUpperId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dot, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.UpperIdPath, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

stmt(tokens: Vec[Token], cursor: U32) (tree: Stmt, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Break, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let label = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Label, ..)):
                let sym = tokens.get(cursor)
                cursor += 1
                sym
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr, val = label)
        )
        let label = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Stmt.Break(label = label.map(|l: Token|: newId(l.text)), level = 0)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Continue, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let label = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Label, ..)):
                let sym = tokens.get(cursor)
                cursor += 1
                sym
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr, val = label)
        )
        let label = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Stmt.Continue(label = label.map(|l: Token|: newId(l.text)), level = 0)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

assignOp(tokens: Vec[Token], cursor: U32) (tree: AssignOp, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Eq, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            AssignOp.Eq
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.PlusEq, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            AssignOp.PlusEq
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.MinusEq, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            AssignOp.MinusEq
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.StarEq, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            AssignOp.StarEq
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.CaretEq, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            AssignOp.CaretEq
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

pat(tokens: Vec[Token], cursor: U32) (tree: Pat, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = simplePat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Pipe, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = simplePat(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

simplePat(tokens: Vec[Token], cursor: U32) (tree: Pat, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let var_ = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Pat.Var(VarPat(var_ = newId(var_.text), ty = Option.None))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = upperIdPath(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let con = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = upperIdPath(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let con = nonTerminalResult.tree
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let nonTerminalResult = recordFieldPat(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            loop:
                let symResult = try(||:
                    if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                        cursor += 1
                    else:
                        throw(
                            ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                    let nonTerminalResult = recordFieldPat(tokens, cursor)
                    cursor = nonTerminalResult.newCursor
                    curErr = nonTerminalResult.newErr
                    (cursor = cursor, err = curErr)
                )
                match symResult:
                    Result.Err(err):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                        break
                    Result.Ok(ok):
                        cursor = ok.cursor
                        curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Pat.Record(RecordPat(fields = Vec.empty(), ignoreRest = Bool.False, inferredTy = Option.None))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = recordFieldPat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let p0 = nonTerminalResult.tree
        let ps = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = recordFieldPat(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let p = nonTerminalResult.tree
                ps.push((p = p))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Pat.Record(RecordPat(
                fields = once(p0).chain(ps.iter().map(|p: (p: Named[Pat])|: p.p)).toVec(),
                ignoreRest = Bool.False,
                inferredTy = Option.None,
            ))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = recordFieldPat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let p0 = nonTerminalResult.tree
        let ps = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = recordFieldPat(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let p = nonTerminalResult.tree
                ps.push((p = p))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let ignoreRest = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Pat.Record(RecordPat(
                fields = once(p0).chain(ps.iter().map(|p: (p: Named[Pat])|: p.p)).toVec(),
                ignoreRest = Bool.True,
                inferredTy = Option.None,
            ))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Underscore, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Pat.Ignore
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let str = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Str, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let nonTerminalResult = strPfxBinder(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let binder = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = binder)
        )
        let binder = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        let value = do:
            Pat.StrPfx(str.text, binder.flatten())
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let char = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Char, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

strPfxBinder(tokens: Vec[Token], cursor: U32) (tree: Option[Id], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let id = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Option.Some(newId(id.text))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Underscore, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Option.None
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordFieldPat(tokens: Vec[Token], cursor: U32) (tree: Named[Pat], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Eq, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = pat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let pat = nonTerminalResult.tree
        let value = do:
            Named(name = Option.Some(newId(name.text)), node = pat)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = pat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let pat = nonTerminalResult.tree
        let value = do:
            Named(name = Option.None, node = pat)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

importDecl(tokens: Vec[Token], cursor: U32) (tree: ImportDecl, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Import, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let p0 = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let ps = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dot, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let p = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
                    let sym = tokens.get(cursor)
                    cursor += 1
                    sym
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                ps.push((p = p))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            let vec: Vec[Str] = once(p0.text).chain(ps.iter().map(|p: (p: Token)|: p.p.text)).toVec()
            ImportDecl(path = vec)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

topFunDecl(tokens: Vec[Token], cursor: U32) (tree: FunDecl, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Prim, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = topFunSig(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = topFunSig(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        loop:
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = topFunSig(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

topFunSig(tokens: Vec[Token], cursor: U32) (tree: (parenTy: Option[Id], sig: FunSig), newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let symResult = try(||:
            let nonTerminalResult = parentTy(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let parentTy = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = parentTy)
        )
        let parentTy = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let nonTerminalResult = context(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let ctx = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = ctx)
        )
        let ctx = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        let nonTerminalResult = paramList(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let params = nonTerminalResult.tree
        let symResult = try(||:
            let nonTerminalResult = returnTy(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let ret = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = ret)
        )
        let ret = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

parentTy(tokens: Vec[Token], cursor: U32) (tree: Id, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let id = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dot, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            newId(id.text)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

context(tokens: Vec[Token], cursor: U32) (tree: Context, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t0 = nonTerminalResult.tree
        let ts = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = type_(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let t = nonTerminalResult.tree
                ts.push((t = t))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Context(
                typeParams = Vec.empty(),
                preds = once(t0).chain(ts.iter().map(|t: (t: Type)|: t.t)).toVec(),
            )
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

paramList(tokens: Vec[Token], cursor: U32) (tree: Vec[(name: Id, ty: Option[Type])], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Vec.empty()
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = param(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let p0 = nonTerminalResult.tree
        let ps = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = param(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let p = nonTerminalResult.tree
                ps.push((p = p))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            let vec: Vec[(name: Id, ty: Option[Type])] =
                once(p0).chain(ps.iter().map(|p: (p: (name: Id, ty: Option[Type]))|: p.p)).toVec()
            vec
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

param(tokens: Vec[Token], cursor: U32) (tree: (name: Id, ty: Option[Type]), newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let nonTerminalResult = type_(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let ty = nonTerminalResult.tree
            let ty = (ty = ty)
            (cursor = cursor, err = curErr, val = ty)
        )
        let ty = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        let value = do:
            (name = newId(name.text), ty = ty.map(|ty: (ty: Type)|: ty.ty))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

traitDecl(tokens: Vec[Token], cursor: U32) (tree: TraitDecl, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Trait, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = typeParams(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let tys = nonTerminalResult.tree
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let nonTerminalResult = traitDeclRhs(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let rhs = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = rhs)
        )
        let rhs = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        let value = do:
            TraitDecl(
                name = newId(name.text),
                typeParams = tys,
                typeParamKinds = Vec.empty(),
                items = rhs.unwrapOr(Vec.empty()),
            )
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

traitDeclRhs(tokens: Vec[Token], cursor: U32) (tree: Vec[FunDecl], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Vec.empty()
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let fs = Vec.empty()
        let nonTerminalResult = funDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let fs = nonTerminalResult.tree
        let fs = Vec.empty()
        loop:
            let symResult = try(||:
                let nonTerminalResult = funDecl(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                fs.push(nonTerminalResult.tree)
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            fs
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

implDecl(tokens: Vec[Token], cursor: U32) (tree: ImplDecl, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Impl, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let nonTerminalResult = context(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            let ctx = nonTerminalResult.tree
            (cursor = cursor, err = curErr, val = ctx)
        )
        let ctx = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t0 = nonTerminalResult.tree
        let ts = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = type_(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let t = nonTerminalResult.tree
                ts.push((t = t))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = implDeclRhs(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let rhs = nonTerminalResult.tree
        let value = do:
            ImplDecl(
                context = ctx.unwrapOr(Context(typeParams = Vec.empty(), preds = Vec.empty())),
                trait_ = newId(name.text),
                tys = once(t0).chain(ts.iter().map(|ts: (t: Type)|: ts.t)).toVec(),
                items = rhs,
            )
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

implDeclRhs(tokens: Vec[Token], cursor: U32) (tree: Vec[FunDecl], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Vec.empty()
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let funs = Vec.empty()
        let nonTerminalResult = funDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let funs = nonTerminalResult.tree
        let funs = Vec.empty()
        loop:
            let symResult = try(||:
                let nonTerminalResult = funDecl(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                funs.push(nonTerminalResult.tree)
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            funs
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

funDecl(tokens: Vec[Token], cursor: U32) (tree: FunDecl, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Prim, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = funSig(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = funSig(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let nonTerminalResult = funDeclRhs(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

funDeclRhs(tokens: Vec[Token], cursor: U32) (tree: Vec[Stmt], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        loop:
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

funSig(tokens: Vec[Token], cursor: U32) (tree: FunSig, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let nonTerminalResult = context(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let nonTerminalResult = paramList(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let symResult = try(||:
            let nonTerminalResult = returnTy(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let value = do:
            panic("TODO")
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
