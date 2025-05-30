# This is generated file, do not edit.

import ParseTree
import Token

type NonTerminal:
    Type_
    NamedType
    RecordTypeField

impl ToStr[NonTerminal]:
    toStr(self: NonTerminal): Str
        match self:
            NonTerminal.Type_: "Type_"
            NonTerminal.NamedType: "NamedType"
            NonTerminal.RecordTypeField: "RecordTypeField"

impl Eq[NonTerminal]:
    __eq(self: NonTerminal, other: NonTerminal): Bool
        match (left = self, right = other):
            (left = NonTerminal.Type_, right = NonTerminal.Type_): Bool.True
            (left = NonTerminal.NamedType, right = NonTerminal.NamedType): Bool.True
            (left = NonTerminal.RecordTypeField, right = NonTerminal.RecordTypeField): Bool.True
            _: Bool.False

type_(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        let nonTerminalResult = namedType(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let symResult = try({
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(tokens.get(cursor)))
                let nonTerminalResult = recordTypeField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            })
            match symResult:
                Result.Err(_):
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        let symResult = try({
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(tokens.get(cursor)))
            cursor
        })
        match symResult:
            Result.Err(_):
                ()
            Result.Ok(newCursor):
                cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let symResult = try({
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(tokens.get(cursor)))
                let nonTerminalResult = recordTypeField(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            })
            match symResult:
                Result.Err(_):
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

namedType(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let symResult = try({
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(tokens.get(cursor)))
                let nonTerminalResult = type_(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            })
            match symResult:
                Result.Err(_):
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        let symResult = try({
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(tokens.get(cursor)))
            cursor
        })
        match symResult:
            Result.Err(_):
                ()
            Result.Ok(newCursor):
                cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

recordTypeField(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes), newCursor = newCursor)
    let altResult = try({
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))
