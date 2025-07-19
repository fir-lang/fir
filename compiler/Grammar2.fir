# This is generated file, do not edit.

import Peg.ParseTree
import Token

type NonTerminal:
    RecordTypeCont

impl ToStr[NonTerminal]:
    toStr(self: NonTerminal) Str:
        match self:
            NonTerminal.RecordTypeCont: "RecordTypeCont"

impl Eq[NonTerminal]:
    __eq(self: NonTerminal, other: NonTerminal) Bool:
        match (left = self, right = other):
            (left = NonTerminal.RecordTypeCont, right = NonTerminal.RecordTypeCont): Bool.True
            _: Bool.False

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
            panic("")
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
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
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
