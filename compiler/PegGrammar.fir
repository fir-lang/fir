# This is generated file, do not edit.

import ParseTree
import Token

type NonTerminal:
    TerminalsDecl
    TerminalDecl

impl ToStr[NonTerminal]:
    toStr(self: NonTerminal): Str
        match self:
            NonTerminal.TerminalsDecl: "TerminalsDecl"
            NonTerminal.TerminalDecl: "TerminalDecl"

terminalsDecl(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)
    let cursor0 = cursor
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try({
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, text = "Terminals", ..):
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let nonTerminalResult = terminalDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let symResult = try({
                let nonTerminalResult = terminalDecl(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                cursor
            })
            match symResult:
                Result.Err(_):
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
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(tokens.get(cursor)))
        let tokensLen0 = tokens.len()
        let symResult = try({
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
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
            let symResult = try({
                let tokensLen0 = tokens.len()
                let symResult = try({
                    if cursor == tokens.len():
                        throw(ParseError.UnexpectedEof)
                    if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
                        nodes.push(ParseTree.Terminal(tokens.get(cursor)))
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
                    break
                Result.Ok(newCursor):
                    cursor = newCursor
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TerminalDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(ParseError.UnexpectedToken(tokens.get(cursor)))
