# This is generated file, do not edit.

import ParseTree
import Token

type InlineExprKind:
    InlineExpr
    PrefixExpr
    Fields
    Args
    SimpleExpr
    UpperIdPath
    TyArgs
    ParenExpr
    ExprPrefix
    BinOp

impl ToStr[InlineExprKind]:
    toStr(self: InlineExprKind) Str:
        match self:
            InlineExprKind.InlineExpr: "InlineExpr"
            InlineExprKind.PrefixExpr: "PrefixExpr"
            InlineExprKind.Fields: "Fields"
            InlineExprKind.Args: "Args"
            InlineExprKind.SimpleExpr: "SimpleExpr"
            InlineExprKind.UpperIdPath: "UpperIdPath"
            InlineExprKind.TyArgs: "TyArgs"
            InlineExprKind.ParenExpr: "ParenExpr"
            InlineExprKind.ExprPrefix: "ExprPrefix"
            InlineExprKind.BinOp: "BinOp"

impl Eq[InlineExprKind]:
    __eq(self: InlineExprKind, other: InlineExprKind) Bool:
        match (left = self, right = other):
            (left = InlineExprKind.InlineExpr, right = InlineExprKind.InlineExpr): Bool.True
            (left = InlineExprKind.PrefixExpr, right = InlineExprKind.PrefixExpr): Bool.True
            (left = InlineExprKind.Fields, right = InlineExprKind.Fields): Bool.True
            (left = InlineExprKind.Args, right = InlineExprKind.Args): Bool.True
            (left = InlineExprKind.SimpleExpr, right = InlineExprKind.SimpleExpr): Bool.True
            (left = InlineExprKind.UpperIdPath, right = InlineExprKind.UpperIdPath): Bool.True
            (left = InlineExprKind.TyArgs, right = InlineExprKind.TyArgs): Bool.True
            (left = InlineExprKind.ParenExpr, right = InlineExprKind.ParenExpr): Bool.True
            (left = InlineExprKind.ExprPrefix, right = InlineExprKind.ExprPrefix): Bool.True
            (left = InlineExprKind.BinOp, right = InlineExprKind.BinOp): Bool.True
            _: Bool.False

inlineExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = prefixExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = binOp(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                let nonTerminalResult = prefixExpr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.InlineExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

prefixExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = exprPrefix(tokens, cursor)
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
        let nonTerminalResult = simpleExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = fields(tokens, cursor)
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = args(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.PrefixExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

fields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
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
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.Fields, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

args(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
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
            let nonTerminalResult = inlineExpr(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            loop:
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
                    let nonTerminalResult = inlineExpr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.Args, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

simpleExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = tyArgs(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = upperIdPath(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = tyArgs(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
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
            let nonTerminalResult = parenExpr(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            loop:
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
                    let nonTerminalResult = parenExpr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Return, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = inlineExpr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Int(_), ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.HexInt(_), ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.BinInt(_), ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Str, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Char, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.SimpleExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

upperIdPath(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
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
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.UpperIdPath, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

tyArgs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.TyArgs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

parenExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
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
        if tokens.get(cursor) is Token(kind = TokenKind.Eq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = inlineExpr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.ParenExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = inlineExpr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.ParenExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

exprPrefix(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Tilde, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.ExprPrefix, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Minus, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.ExprPrefix, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

binOp(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, InlineExprKind], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, InlineExprKind]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Plus, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.BinOp, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Minus, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.BinOp, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Star, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.BinOp, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Slash, ..):
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
            return (tree = ParseTree.NonTerminal(kind = InlineExprKind.BinOp, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))
