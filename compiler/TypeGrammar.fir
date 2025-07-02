# This is generated file, do not edit.

import ParseTree
import Token

type NonTerminal:
    Type_
    RecordType
    VariantType
    FnType
    NamedType
    RecordTypeFields
    RecordTypeField
    VariantAlt
    FnArgs
    ReturnType
    TypeDecl
    TypeParams
    TypeDeclRhs
    ConDecl
    NamedFields
    NamedField
    UnnamedFields

impl ToStr[NonTerminal]:
    toStr(self: NonTerminal) Str:
        match self:
            NonTerminal.Type_: "Type_"
            NonTerminal.RecordType: "RecordType"
            NonTerminal.VariantType: "VariantType"
            NonTerminal.FnType: "FnType"
            NonTerminal.NamedType: "NamedType"
            NonTerminal.RecordTypeFields: "RecordTypeFields"
            NonTerminal.RecordTypeField: "RecordTypeField"
            NonTerminal.VariantAlt: "VariantAlt"
            NonTerminal.FnArgs: "FnArgs"
            NonTerminal.ReturnType: "ReturnType"
            NonTerminal.TypeDecl: "TypeDecl"
            NonTerminal.TypeParams: "TypeParams"
            NonTerminal.TypeDeclRhs: "TypeDeclRhs"
            NonTerminal.ConDecl: "ConDecl"
            NonTerminal.NamedFields: "NamedFields"
            NonTerminal.NamedField: "NamedField"
            NonTerminal.UnnamedFields: "UnnamedFields"

impl Eq[NonTerminal]:
    __eq(self: NonTerminal, other: NonTerminal) Bool:
        match (left = self, right = other):
            (left = NonTerminal.Type_, right = NonTerminal.Type_): Bool.True
            (left = NonTerminal.RecordType, right = NonTerminal.RecordType): Bool.True
            (left = NonTerminal.VariantType, right = NonTerminal.VariantType): Bool.True
            (left = NonTerminal.FnType, right = NonTerminal.FnType): Bool.True
            (left = NonTerminal.NamedType, right = NonTerminal.NamedType): Bool.True
            (left = NonTerminal.RecordTypeFields, right = NonTerminal.RecordTypeFields): Bool.True
            (left = NonTerminal.RecordTypeField, right = NonTerminal.RecordTypeField): Bool.True
            (left = NonTerminal.VariantAlt, right = NonTerminal.VariantAlt): Bool.True
            (left = NonTerminal.FnArgs, right = NonTerminal.FnArgs): Bool.True
            (left = NonTerminal.ReturnType, right = NonTerminal.ReturnType): Bool.True
            (left = NonTerminal.TypeDecl, right = NonTerminal.TypeDecl): Bool.True
            (left = NonTerminal.TypeParams, right = NonTerminal.TypeParams): Bool.True
            (left = NonTerminal.TypeDeclRhs, right = NonTerminal.TypeDeclRhs): Bool.True
            (left = NonTerminal.ConDecl, right = NonTerminal.ConDecl): Bool.True
            (left = NonTerminal.NamedFields, right = NonTerminal.NamedFields): Bool.True
            (left = NonTerminal.NamedField, right = NonTerminal.NamedField): Bool.True
            (left = NonTerminal.UnnamedFields, right = NonTerminal.UnnamedFields): Bool.True
            _: Bool.False

type_(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = namedType(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId | TokenKind.Self_, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = recordType(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = variantType(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = fnType(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

recordType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = recordTypeFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

variantType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = variantAlt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = variantAlt(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId | TokenKind.Self_, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = variantAlt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = variantAlt(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

fnType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperFn, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = fnArgs(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = returnType(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FnType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

namedType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = type_(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

recordTypeFields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = recordTypeField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId | TokenKind.Self_, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeFields, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = recordTypeField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeFields, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

recordTypeField(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId | TokenKind.Self_, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

variantAlt(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = recordTypeFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantAlt, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantAlt, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

fnArgs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = type_(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FnArgs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

returnType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = type_(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ReturnType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

typeDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Type, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = typeDeclRhs(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDecl, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Type, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDecl, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Prim, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Type, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

typeParams(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId | TokenKind.Self_, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.LowerId | TokenKind.Self_, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeParams, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId | TokenKind.Self_, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeParams, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

typeDeclRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = conDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = conDecl(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDeclRhs, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = namedField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = namedField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDeclRhs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

conDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = namedFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ConDecl, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = unnamedFields(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ConDecl, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ConDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

namedFields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = namedField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = namedField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedFields, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

namedField(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId | TokenKind.Self_, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedField, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

unnamedFields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = type_(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            )
            match symResult:
                Result.Err(err):
                    match curErr:
                        Option.None:
                            curErr = Option.Some(err)
                        Option.Some(curErr_):
                            curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            cursor
        )
        match symResult:
            Result.Err(err):
                match curErr:
                    Option.None:
                        curErr = Option.Some(err)
                    Option.Some(curErr_):
                        curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        cursor
    )
    match altResult:
        Result.Err(err):
            match curErr:
                Option.None:
                    curErr = Option.Some(err)
                Option.Some(curErr_):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.UnnamedFields, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))
