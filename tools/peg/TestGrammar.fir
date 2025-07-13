# This is generated file, do not edit.

import Compiler.Token
import Peg.ParseTree

type NonTerminal:
    TerminalA
    TerminalB
    TerminalAOrB
    TerminalAThenB
    ZeroOrMoreAThenB
    OneOrMoreAThenB
    ZeroOrOneAThenB
    IgnoreAThenB
    IgnoreAThenIgnoreB
    IgnoreGroupAThenB
    NonTerminals
    NonTerminalsBacktrack
    NegLookahead
    EndOfInputTest
    BracketedOneOrMoreA

impl ToStr[NonTerminal]:
    toStr(self: NonTerminal) Str:
        match self:
            NonTerminal.TerminalA: "TerminalA"
            NonTerminal.TerminalB: "TerminalB"
            NonTerminal.TerminalAOrB: "TerminalAOrB"
            NonTerminal.TerminalAThenB: "TerminalAThenB"
            NonTerminal.ZeroOrMoreAThenB: "ZeroOrMoreAThenB"
            NonTerminal.OneOrMoreAThenB: "OneOrMoreAThenB"
            NonTerminal.ZeroOrOneAThenB: "ZeroOrOneAThenB"
            NonTerminal.IgnoreAThenB: "IgnoreAThenB"
            NonTerminal.IgnoreAThenIgnoreB: "IgnoreAThenIgnoreB"
            NonTerminal.IgnoreGroupAThenB: "IgnoreGroupAThenB"
            NonTerminal.NonTerminals: "NonTerminals"
            NonTerminal.NonTerminalsBacktrack: "NonTerminalsBacktrack"
            NonTerminal.NegLookahead: "NegLookahead"
            NonTerminal.EndOfInputTest: "EndOfInputTest"
            NonTerminal.BracketedOneOrMoreA: "BracketedOneOrMoreA"

impl Eq[NonTerminal]:
    __eq(self: NonTerminal, other: NonTerminal) Bool:
        match (left = self, right = other):
            (left = NonTerminal.TerminalA, right = NonTerminal.TerminalA): Bool.True
            (left = NonTerminal.TerminalB, right = NonTerminal.TerminalB): Bool.True
            (left = NonTerminal.TerminalAOrB, right = NonTerminal.TerminalAOrB): Bool.True
            (left = NonTerminal.TerminalAThenB, right = NonTerminal.TerminalAThenB): Bool.True
            (left = NonTerminal.ZeroOrMoreAThenB, right = NonTerminal.ZeroOrMoreAThenB): Bool.True
            (left = NonTerminal.OneOrMoreAThenB, right = NonTerminal.OneOrMoreAThenB): Bool.True
            (left = NonTerminal.ZeroOrOneAThenB, right = NonTerminal.ZeroOrOneAThenB): Bool.True
            (left = NonTerminal.IgnoreAThenB, right = NonTerminal.IgnoreAThenB): Bool.True
            (left = NonTerminal.IgnoreAThenIgnoreB, right = NonTerminal.IgnoreAThenIgnoreB): Bool.True
            (left = NonTerminal.IgnoreGroupAThenB, right = NonTerminal.IgnoreGroupAThenB): Bool.True
            (left = NonTerminal.NonTerminals, right = NonTerminal.NonTerminals): Bool.True
            (left = NonTerminal.NonTerminalsBacktrack, right = NonTerminal.NonTerminalsBacktrack): Bool.True
            (left = NonTerminal.NegLookahead, right = NonTerminal.NegLookahead): Bool.True
            (left = NonTerminal.EndOfInputTest, right = NonTerminal.EndOfInputTest): Bool.True
            (left = NonTerminal.BracketedOneOrMoreA, right = NonTerminal.BracketedOneOrMoreA): Bool.True
            _: Bool.False

terminalA(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TerminalA, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

terminalB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TerminalB, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

terminalAOrB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TerminalAOrB, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TerminalAOrB, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

terminalAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TerminalAThenB, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

zeroOrMoreAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ZeroOrMoreAThenB, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

oneOrMoreAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.OneOrMoreAThenB, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

zeroOrOneAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ZeroOrOneAThenB, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

ignoreAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IgnoreAThenB, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

ignoreAThenIgnoreB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IgnoreAThenIgnoreB, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

ignoreGroupAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IgnoreGroupAThenB, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

nonTerminals(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = terminalAOrB(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = terminalAOrB(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminals, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

nonTerminalsBacktrack(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = terminalAOrB(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = terminalAOrB(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalsBacktrack, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalsBacktrack, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

negLookahead(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let tokensLen0 = tokens.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                tokens.truncate(tokensLen0)
            Result.Ok(_):
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = terminalAOrB(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NegLookahead, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

endOfInputTest(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if cursor == tokens.len():
            cursor
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.EndOfInputTest, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

bracketedOneOrMoreA(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = oneOrMoreAThenB(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                nodes.push(nonTerminalResult.tree)
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
        if cursor == tokens.len():
            cursor
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.BracketedOneOrMoreA, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
