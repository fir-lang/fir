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
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalA, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

terminalB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalB, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

terminalAOrB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalAOrB, nodes)
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalAOrB, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

terminalAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalAThenB, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

zeroOrMoreAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.ZeroOrMoreAThenB, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

oneOrMoreAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.OneOrMoreAThenB, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

zeroOrOneAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.ZeroOrOneAThenB, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

ignoreAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IgnoreAThenB, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

ignoreAThenIgnoreB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IgnoreAThenIgnoreB, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

ignoreGroupAThenB(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IgnoreGroupAThenB, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

nonTerminals(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = terminalAOrB(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = terminalAOrB(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminals, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

nonTerminalsBacktrack(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = terminalAOrB(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = terminalAOrB(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalsBacktrack, nodes)
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
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalsBacktrack, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

negLookahead(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NegLookahead, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

endOfInputTest(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.EndOfInputTest, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

bracketedOneOrMoreA(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.BracketedOneOrMoreA, nodes)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

semanticActionSimple(tokens: Vec[Token], cursor: U32) (tree: Char, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            'a'
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            'b'
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

semanticActionZeroOrMore(tokens: Vec[Token], cursor: U32) (tree: Vec[Char], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let cs = Vec.empty()
        loop:
            let symResult = try(||:
                let nonTerminalResult = semanticActionSimple(tokens, cursor)
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
            cs
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

semanticActionOneOrMore(tokens: Vec[Token], cursor: U32) (tree: Vec[Char], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let cs = Vec.empty()
        let nonTerminalResult = semanticActionSimple(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        cs.push(nonTerminalResult.tree)
        loop:
            let symResult = try(||:
                let nonTerminalResult = semanticActionSimple(tokens, cursor)
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
            cs
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

semanticActionGroup(tokens: Vec[Token], cursor: U32) (tree: Vec[Str], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let a = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let b = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let ab = (a = a, b = b)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            let strs: Vec[Str] = Vec.[ab.a.text, ab.b.text]
            strs
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

semanticActionOptional(tokens: Vec[Token], cursor: U32) (tree: Option[Token], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let symResult = try(||:
            let cs = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
                let sym = tokens.get(cursor)
                cursor += 1
                sym
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr, val = cs)
        )
        let cs = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if cursor == tokens.len():
            cursor
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            cs
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

semanticActionComplex(tokens: Vec[Token], cursor: U32) (tree: (aVec: Vec[Token], bVec: Vec[Token], cOpt: Option[Token]), newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let aVec = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
                    aVec.push(tokens.get(cursor))
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let bVec = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            bVec.push(tokens.get(cursor))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
                    bVec.push(tokens.get(cursor))
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
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
            let cOpt = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
                let sym = tokens.get(cursor)
                cursor += 1
                sym
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr, val = cOpt)
        )
        let cOpt = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        let group = (aVec = aVec, bVec = bVec, cOpt = cOpt)
        if cursor == tokens.len():
            cursor
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            group
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

cursorPositions(tokens: Vec[Token], cursor: U32) (tree: Vec[U32], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let c0 = cursor
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let c1 = cursor
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let c2 = cursor
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let c3 = cursor
        let value = do:
            let vec: Vec[U32] = Vec.[c0, c1, c2, c3]
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

simpleGroup1(tokens: Vec[Token], cursor: U32) (tree: Token, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let x = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            x
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

simpleGroup2(tokens: Vec[Token], cursor: U32) (tree: Option[Token], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            let x = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
                let sym = tokens.get(cursor)
                cursor += 1
                sym
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr, val = x)
        )
        let x = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            x
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

simpleGroup3(tokens: Vec[Token], cursor: U32) (tree: Vec[Token], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let x = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
                    x.push(tokens.get(cursor))
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            x
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

simpleGroup4(tokens: Vec[Token], cursor: U32) (tree: Vec[Token], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let x = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            x.push(tokens.get(cursor))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
                    x.push(tokens.get(cursor))
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            x
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

simpleGroup5(tokens: Vec[Token], cursor: U32) (tree: Option[Token], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let x = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
                let sym = tokens.get(cursor)
                cursor += 1
                sym
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr, val = x)
        )
        let x = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
                Option.Some(ok.val)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            x
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

simpleGroup6(tokens: Vec[Token], cursor: U32) (tree: Vec[Token], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let x = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
                    x.push(tokens.get(cursor))
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            x
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

simpleGroup7(tokens: Vec[Token], cursor: U32) (tree: Vec[Token], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let x = Vec.empty()
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
            x.push(tokens.get(cursor))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "a", ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "b", ..)):
                    x.push(tokens.get(cursor))
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, text = "c", ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            x
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
