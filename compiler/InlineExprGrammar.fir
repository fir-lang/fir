# This is generated file, do not edit.

import ParseTree
import Token
import TypeGrammar

type InlineExprKind:
    InlineExpr
    SimpleInlineExpr
    UpperIdPath
    TyArgs
    ParenExpr

impl ToStr[InlineExprKind]:
    toStr(self: InlineExprKind) Str:
        match self:
            InlineExprKind.InlineExpr: "InlineExpr"
            InlineExprKind.SimpleInlineExpr: "SimpleInlineExpr"
            InlineExprKind.UpperIdPath: "UpperIdPath"
            InlineExprKind.TyArgs: "TyArgs"
            InlineExprKind.ParenExpr: "ParenExpr"

impl Eq[InlineExprKind]:
    __eq(self: InlineExprKind, other: InlineExprKind) Bool:
        match (left = self, right = other):
            (left = InlineExprKind.InlineExpr, right = InlineExprKind.InlineExpr): Bool.True
            (left = InlineExprKind.SimpleInlineExpr, right = InlineExprKind.SimpleInlineExpr): Bool.True
            (left = InlineExprKind.UpperIdPath, right = InlineExprKind.UpperIdPath): Bool.True
            (left = InlineExprKind.TyArgs, right = InlineExprKind.TyArgs): Bool.True
            (left = InlineExprKind.ParenExpr, right = InlineExprKind.ParenExpr): Bool.True
            _: Bool.False

inlineExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try({
        let nodesLen0 = nodes.len()
        let symResult = try({
            let nonTerminalResult = exprPrefix(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            cursor
        })
        match symResult:
            Result.Err(_):
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        let nonTerminalResult = simpleInlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try({
            let nonTerminalResult = exprSuffix(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            cursor
        })
        match symResult:
            Result.Err(_):
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try({
                let nodesLen0 = nodes.len()
                let symResult = try({
                    let nonTerminalResult = exprPrefix(tokens, cursor)
                    cursor = nonTerminalResult.newCursor
                    nodes.push(nonTerminalResult.tree)
                    cursor
                })
                match symResult:
                    Result.Err(_):
                        nodes.truncate(nodesLen0)
                    Result.Ok(newCursor):
                        cursor = newCursor
                let nonTerminalResult = simpleInlineExpr(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                let nodesLen0 = nodes.len()
                let symResult = try({
                    let nonTerminalResult = exprSuffix(tokens, cursor)
                    cursor = nonTerminalResult.newCursor
                    nodes.push(nonTerminalResult.tree)
                    cursor
                })
                match symResult:
                    Result.Err(_):
                        nodes.truncate(nodesLen0)
                    Result.Ok(newCursor):
                        cursor = newCursor
                cursor
            })
            match symResult:
                Result.Err(_):
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.InlineExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

simpleInlineExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId | TokenKind.Self_, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nodesLen0 = nodes.len()
        let symResult = try({
            let nonTerminalResult = tyArgs(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            cursor
        })
        match symResult:
            Result.Err(_):
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleInlineExpr, nodes), newCursor = newCursor)
    let altResult = try({
        let nonTerminalResult = upperIdPath(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try({
            let nonTerminalResult = tyArgs(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            cursor
        })
        match symResult:
            Result.Err(_):
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleInlineExpr, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nodesLen0 = nodes.len()
        let symResult = try({
            let nonTerminalResult = parenExpr(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            loop:
                let nodesLen0 = nodes.len()
                let symResult = try({
                    if cursor == tokens.len():
                        throw(ParseError.UnexpectedEof)
                    if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                        nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                        cursor += 1
                    else:
                        throw(ParseError.UnexpectedToken(tokens.get(cursor)))
                    let nonTerminalResult = parenExpr(tokens, cursor)
                    cursor = nonTerminalResult.newCursor
                    nodes.push(nonTerminalResult.tree)
                    cursor
                })
                match symResult:
                    Result.Err(_):
                        nodes.truncate(nodesLen0)
                        break
                    Result.Ok(newCursor):
                        cursor = newCursor
            let nodesLen0 = nodes.len()
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
                    nodes.truncate(nodesLen0)
                Result.Ok(newCursor):
                    cursor = newCursor
            cursor
        })
        match symResult:
            Result.Err(_):
                nodes.truncate(nodesLen0)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleInlineExpr, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Return, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleInlineExpr, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Int(_)):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleInlineExpr, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.HexInt(_)):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleInlineExpr, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.BinInt(_)):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleInlineExpr, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Str(_)):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleInlineExpr, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Char(_)):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleInlineExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

upperIdPath(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try({
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(tokens.get(cursor)))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(tokens.get(cursor)))
                cursor
            })
            match symResult:
                Result.Err(_):
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.UpperIdPath, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

tyArgs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try({
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
            let nodesLen0 = nodes.len()
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
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        let nodesLen0 = nodes.len()
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
                nodes.truncate(nodesLen0)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.TyArgs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

parenExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId | TokenKind.Self_, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Eq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.ParenExpr, nodes), newCursor = newCursor)
    let altResult = try({
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.ParenExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))
