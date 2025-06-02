# This is generated file, do not edit.

import ParseTree
import Token

type NonTerminal:
    Grammar
    ImportDecls
    ImportDecl
    TypeDecls
    TypeDecl
    TerminalsDecl
    TerminalDecl
    NonTerminalDecls
    NonTerminalDecl
    NonTerminalAlt
    Symbol
    SymbolPrefix
    SymbolNonRec
    SymbolSuffix

impl ToStr[NonTerminal]:
    toStr(self: NonTerminal): Str
        match self:
            NonTerminal.Grammar: "Grammar"
            NonTerminal.ImportDecls: "ImportDecls"
            NonTerminal.ImportDecl: "ImportDecl"
            NonTerminal.TypeDecls: "TypeDecls"
            NonTerminal.TypeDecl: "TypeDecl"
            NonTerminal.TerminalsDecl: "TerminalsDecl"
            NonTerminal.TerminalDecl: "TerminalDecl"
            NonTerminal.NonTerminalDecls: "NonTerminalDecls"
            NonTerminal.NonTerminalDecl: "NonTerminalDecl"
            NonTerminal.NonTerminalAlt: "NonTerminalAlt"
            NonTerminal.Symbol: "Symbol"
            NonTerminal.SymbolPrefix: "SymbolPrefix"
            NonTerminal.SymbolNonRec: "SymbolNonRec"
            NonTerminal.SymbolSuffix: "SymbolSuffix"

impl Eq[NonTerminal]:
    __eq(self: NonTerminal, other: NonTerminal): Bool
        match (left = self, right = other):
            (left = NonTerminal.Grammar, right = NonTerminal.Grammar): Bool.True
            (left = NonTerminal.ImportDecls, right = NonTerminal.ImportDecls): Bool.True
            (left = NonTerminal.ImportDecl, right = NonTerminal.ImportDecl): Bool.True
            (left = NonTerminal.TypeDecls, right = NonTerminal.TypeDecls): Bool.True
            (left = NonTerminal.TypeDecl, right = NonTerminal.TypeDecl): Bool.True
            (left = NonTerminal.TerminalsDecl, right = NonTerminal.TerminalsDecl): Bool.True
            (left = NonTerminal.TerminalDecl, right = NonTerminal.TerminalDecl): Bool.True
            (left = NonTerminal.NonTerminalDecls, right = NonTerminal.NonTerminalDecls): Bool.True
            (left = NonTerminal.NonTerminalDecl, right = NonTerminal.NonTerminalDecl): Bool.True
            (left = NonTerminal.NonTerminalAlt, right = NonTerminal.NonTerminalAlt): Bool.True
            (left = NonTerminal.Symbol, right = NonTerminal.Symbol): Bool.True
            (left = NonTerminal.SymbolPrefix, right = NonTerminal.SymbolPrefix): Bool.True
            (left = NonTerminal.SymbolNonRec, right = NonTerminal.SymbolNonRec): Bool.True
            (left = NonTerminal.SymbolSuffix, right = NonTerminal.SymbolSuffix): Bool.True
            _: Bool.False

grammar(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        let nonTerminalResult = importDecls(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = typeDecls(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = terminalsDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = nonTerminalDecls(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Grammar, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

importDecls(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try({
                let nonTerminalResult = importDecl(tokens, cursor)
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
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ImportDecls, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

importDecl(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Import, ..):
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
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try({
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ImportDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

typeDecls(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try({
                let nonTerminalResult = typeDecl(tokens, cursor)
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
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDecls, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

typeDecl(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Type, ..):
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Eq, ..):
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

terminalsDecl(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        let nodesLen0 = nodes.len()
        let symResult = try({
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.UpperId, text = "Terminals", ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(tokens.get(cursor)))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(tokens.get(cursor)))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(tokens.get(cursor)))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(tokens.get(cursor)))
            let nonTerminalResult = terminalDecl(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            loop:
                let nodesLen0 = nodes.len()
                let symResult = try({
                    let nonTerminalResult = terminalDecl(tokens, cursor)
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
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
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
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TerminalsDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

terminalDecl(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Str, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Eq, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let tokensLen0 = tokens.len()
        let symResult = try({
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        })
        match symResult:
            Result.Err(_):
                tokens.truncate(tokensLen0)
            Result.Ok(_):
                throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try({
                let tokensLen0 = tokens.len()
                let symResult = try({
                    if cursor == tokens.len():
                        throw(ParseError.UnexpectedEof)
                    if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
                        cursor += 1
                    else:
                        throw(ParseError.UnexpectedToken(tokens.get(cursor)))
                })
                match symResult:
                    Result.Err(_):
                        tokens.truncate(tokensLen0)
                    Result.Ok(_):
                        throw(ParseError.UnexpectedToken(tokens.get(cursor)))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(..):
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TerminalDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

nonTerminalDecls(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try({
                let nonTerminalResult = nonTerminalDecl(tokens, cursor)
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
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalDecls, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

nonTerminalDecl(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
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
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nonTerminalResult = nonTerminalAlt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try({
                let nonTerminalResult = nonTerminalAlt(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

nonTerminalAlt(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        let nonTerminalResult = symbol(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try({
                let nonTerminalResult = symbol(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalAlt, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

symbol(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        let nodesLen0 = nodes.len()
        let symResult = try({
            let nonTerminalResult = symbolPrefix(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            cursor
        })
        match symResult:
            Result.Err(_):
                nodes.truncate(nodesLen0)
            Result.Ok(newCursor):
                cursor = newCursor
        let nonTerminalResult = symbolNonRec(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try({
            let nonTerminalResult = symbolSuffix(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Symbol, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

symbolPrefix(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Minus, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Underscore, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

symbolNonRec(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
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
        cursor
    })
    match altResult:
        Result.Err(err):
            cursor = cursor0
            nodes.clear()
        Result.Ok(newCursor):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolNonRec, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Str, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolNonRec, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nonTerminalResult = symbol(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try({
                let nonTerminalResult = symbol(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolNonRec, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))

symbolSuffix(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Star, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolSuffix, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Plus, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolSuffix, nodes), newCursor = newCursor)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Question, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolSuffix, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))
