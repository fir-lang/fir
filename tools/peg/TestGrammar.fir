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
    ErrorCursorBug
    ErrorCursorBugAlt1
    ErrorCursorBugAlt2


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
            NonTerminal.ErrorCursorBug: "ErrorCursorBug"
            NonTerminal.ErrorCursorBugAlt1: "ErrorCursorBugAlt1"
            NonTerminal.ErrorCursorBugAlt2: "ErrorCursorBugAlt2"


impl Eq[NonTerminal]:
    __eq(self: NonTerminal, other: NonTerminal) Bool:
        match (left = self, right = other):
            (left = NonTerminal.TerminalA, right = NonTerminal.TerminalA):
                Bool.True
            (left = NonTerminal.TerminalB, right = NonTerminal.TerminalB):
                Bool.True
            (left = NonTerminal.TerminalAOrB, right = NonTerminal.TerminalAOrB):
                Bool.True
            (
                left = NonTerminal.TerminalAThenB,
                right = NonTerminal.TerminalAThenB,
            ): Bool.True
            (
                left = NonTerminal.ZeroOrMoreAThenB,
                right = NonTerminal.ZeroOrMoreAThenB,
            ): Bool.True
            (
                left = NonTerminal.OneOrMoreAThenB,
                right = NonTerminal.OneOrMoreAThenB,
            ): Bool.True
            (
                left = NonTerminal.ZeroOrOneAThenB,
                right = NonTerminal.ZeroOrOneAThenB,
            ): Bool.True
            (left = NonTerminal.IgnoreAThenB, right = NonTerminal.IgnoreAThenB):
                Bool.True
            (
                left = NonTerminal.IgnoreAThenIgnoreB,
                right = NonTerminal.IgnoreAThenIgnoreB,
            ): Bool.True
            (
                left = NonTerminal.IgnoreGroupAThenB,
                right = NonTerminal.IgnoreGroupAThenB,
            ): Bool.True
            (left = NonTerminal.NonTerminals, right = NonTerminal.NonTerminals):
                Bool.True
            (
                left = NonTerminal.NonTerminalsBacktrack,
                right = NonTerminal.NonTerminalsBacktrack,
            ): Bool.True
            (left = NonTerminal.NegLookahead, right = NonTerminal.NegLookahead):
                Bool.True
            (
                left = NonTerminal.EndOfInputTest,
                right = NonTerminal.EndOfInputTest,
            ): Bool.True
            (
                left = NonTerminal.BracketedOneOrMoreA,
                right = NonTerminal.BracketedOneOrMoreA,
            ): Bool.True
            (
                left = NonTerminal.ErrorCursorBug,
                right = NonTerminal.ErrorCursorBug,
            ): Bool.True
            (
                left = NonTerminal.ErrorCursorBugAlt1,
                right = NonTerminal.ErrorCursorBugAlt1,
            ): Bool.True
            (
                left = NonTerminal.ErrorCursorBugAlt2,
                right = NonTerminal.ErrorCursorBugAlt2,
            ): Bool.True
            _: Bool.False


terminalA(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.TerminalA, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


terminalB(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.TerminalB, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


terminalAOrB(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.TerminalAOrB, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.TerminalAOrB, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


terminalAThenB(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.TerminalAThenB, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


zeroOrMoreAThenB(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let nodesLen0 = nodes.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "a",
                                        ..
                                    ):
                            nodes.push(ParseTree.Terminal(sym))
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        nodes.truncate(nodesLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.ZeroOrMoreAThenB, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


oneOrMoreAThenB(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let nodesLen0 = nodes.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "a",
                                        ..
                                    ):
                            nodes.push(ParseTree.Terminal(sym))
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        nodes.truncate(nodesLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.OneOrMoreAThenB, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


zeroOrOneAThenB(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            let optionalCursor0 = state._cursor
            let nodesLen0 = nodes.len()
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "a",
                                    ..
                                ):
                        nodes.push(ParseTree.Terminal(sym))
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    nodes.truncate(nodesLen0)
                Result.Ok(ok): ()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.ZeroOrOneAThenB, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


ignoreAThenB(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.IgnoreAThenB, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


ignoreAThenIgnoreB(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(
                    kind = NonTerminal.IgnoreAThenIgnoreB,
                    nodes,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


ignoreGroupAThenB(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(
                    kind = NonTerminal.IgnoreGroupAThenB,
                    nodes,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


nonTerminals(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            nodes.push(terminalAOrB(state))
            nodes.push(terminalAOrB(state))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.NonTerminals, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


nonTerminalsBacktrack(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            nodes.push(terminalAOrB(state))
            nodes.push(terminalAOrB(state))
            let value = do:
                ParseTree.NonTerminal(
                    kind = NonTerminal.NonTerminalsBacktrack,
                    nodes,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(
                    kind = NonTerminal.NonTerminalsBacktrack,
                    nodes,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


negLookahead(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            let state0 = state.clone()
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "a",
                                    ..
                                ):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor)),
            )
            match symResult:
                Result.Err(err): state.cloneFrom(state0)
                Result.Ok(_):
                    state.cloneFrom(state0)
                    throw(state.updateErrorCursor(state._cursor))
            nodes.push(terminalAOrB(state))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.NegLookahead, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


endOfInputTest(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek().isNone():
                state._cursor
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.EndOfInputTest, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


bracketedOneOrMoreA(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let nodesLen0 = nodes.len()
                let symResult = try(||: nodes.push(oneOrMoreAThenB(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        nodes.truncate(nodesLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek().isNone():
                state._cursor
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(
                    kind = NonTerminal.BracketedOneOrMoreA,
                    nodes,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


semanticActionSimple(state: ParserState[Token]) Char / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                'a'
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                'b'
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


semanticActionZeroOrMore(state: ParserState[Token]) Vec[Char] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let zeroOrMoreCursor0 = state._cursor
            let cs = Vec.empty()
            loop:
                let csLen0 = cs.len()
                let symResult = try(||: cs.push(semanticActionSimple(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        cs.truncate(csLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let value = do:
                cs
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


semanticActionOneOrMore(state: ParserState[Token]) Vec[Char] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let cs = Vec.empty()
            cs.push(semanticActionSimple(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let csLen0 = cs.len()
                let symResult = try(||: cs.push(semanticActionSimple(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        cs.truncate(csLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let value = do:
                cs
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


semanticActionGroup(state: ParserState[Token]) Vec[Str] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let a = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let b = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            let ab = (a = a, b = b)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                let strs: Vec[Str] = Vec.[ab.a.text, ab.b.text]
                strs
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


semanticActionOptional(state: ParserState[Token]) Option[Token] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    let cs = if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "a",
                                    ..
                                ):
                        state._cursor += 1
                        sym
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    cs,
            )
            let cs = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek().isNone():
                state._cursor
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                cs
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


semanticActionComplex(state: ParserState[Token]) (aVec: Vec[Token], bVec: Vec[Token], cOpt: Option[Token]) / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            let aVec = Vec.empty()
            loop:
                let aVecLen0 = aVec.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "a",
                                        ..
                                    ):
                            aVec.push(sym)
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        aVec.truncate(aVecLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let bVec = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                bVec.push(sym)
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let bVecLen0 = bVec.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "b",
                                        ..
                                    ):
                            bVec.push(sym)
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        bVec.truncate(bVecLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    let cOpt = if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "c",
                                    ..
                                ):
                        state._cursor += 1
                        sym
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    cOpt,
            )
            let cOpt = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let group = (aVec = aVec, bVec = bVec, cOpt = cOpt)
            if state.peek().isNone():
                state._cursor
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                group
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


cursorPositions(state: ParserState[Token]) Vec[U32] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let c0 = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let c1 = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let c2 = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let c3 = state.nextCursor()
            let value = do:
                let vec: Vec[U32] = Vec.[c0, c1, c2, c3]
                vec
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


simpleGroup1(state: ParserState[Token]) Token / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let x = if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
                sym
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                x
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


simpleGroup2(state: ParserState[Token]) Option[Token] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    let x = if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "b",
                                    ..
                                ):
                        state._cursor += 1
                        sym
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    x,
            )
            let x = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                x
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


simpleGroup3(state: ParserState[Token]) Vec[Token] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            let x = Vec.empty()
            loop:
                let xLen0 = x.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "b",
                                        ..
                                    ):
                            x.push(sym)
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        x.truncate(xLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                x
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


simpleGroup4(state: ParserState[Token]) Vec[Token] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let x = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                x.push(sym)
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let xLen0 = x.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "b",
                                        ..
                                    ):
                            x.push(sym)
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        x.truncate(xLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                x
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


simpleGroup5(state: ParserState[Token]) Option[Token] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "a",
                                    ..
                                ):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let x = if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "b",
                                    ..
                                ):
                        state._cursor += 1
                        sym
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "c",
                                    ..
                                ):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    x,
            )
            let x = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                x
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


simpleGroup6(state: ParserState[Token]) Vec[Token] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            let x = Vec.empty()
            loop:
                let xLen0 = x.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "a",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "b",
                                        ..
                                    ):
                            x.push(sym)
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "c",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        x.truncate(xLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                x
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


simpleGroup7(state: ParserState[Token]) Vec[Token] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let x = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                x.push(sym)
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let xLen0 = x.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "a",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "b",
                                        ..
                                    ):
                            x.push(sym)
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "c",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        x.truncate(xLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                x
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


multipleSymbols(state: ParserState[Token]) Bool / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Bool.True
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


restoreCursorOptional1(state: ParserState[Token]) Option[Bool] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    let x = multipleSymbols(state)
                    x,
            )
            let x = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                x
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


restoreCursorOptional2(state: ParserState[Token]) Bool / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "a",
                                    ..
                                ):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "b",
                                    ..
                                ):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "c",
                                    ..
                                ):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Bool.True
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


restoreCursorZeroOrMore1(state: ParserState[Token]) Vec[Bool] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let zeroOrMoreCursor0 = state._cursor
            let xs = Vec.empty()
            loop:
                let xsLen0 = xs.len()
                let symResult = try(||: xs.push(multipleSymbols(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        xs.truncate(xsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                xs
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


restoreCursorZeroOrMore2(state: ParserState[Token]) Bool / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "a",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "b",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "c",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Bool.True
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


restoreCursorOneOrMore1(state: ParserState[Token]) Vec[Bool] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let xs = Vec.empty()
            xs.push(multipleSymbols(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let xsLen0 = xs.len()
                let symResult = try(||: xs.push(multipleSymbols(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        xs.truncate(xsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                xs
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


restoreCursorOneOrMore2(state: ParserState[Token]) Bool / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "a",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "b",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "c",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                Bool.True
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


zeroOrMoreResultBug1(state: ParserState[Token]) U32 / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            let v = Vec.empty()
            loop:
                let vLen0 = v.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        v.push(state.nextCursor())
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "b",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        v.truncate(vLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let value = do:
                v.len()
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


zeroOrMoreResultBug2(state: ParserState[Token]) Option[U32] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    let v = state.nextCursor()
                    if state.peek() is Option.Some(sym)
                            and sym
                                is Token(
                                    kind = TokenKind.LowerId,
                                    text = "b",
                                    ..
                                ):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    v,
            )
            let v = match symResult:
                Result.Err(err):
                    state._cursor = optionalCursor0
                    Option.None
                Result.Ok(ok):
                    ()
                    Option.Some(ok)
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let value = do:
                v
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


zeroOrMoreResultBug3(state: ParserState[Token]) U32 / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let v = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.Comma, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            v.push(state.nextCursor())
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let vLen0 = v.len()
                let symResult = try(
                    ||:
                        if state.peek() is Option.Some(sym)
                                and sym is Token(kind = TokenKind.Comma, ..):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor))
                        v.push(state.nextCursor())
                        if state.peek() is Option.Some(sym)
                                and sym
                                    is Token(
                                        kind = TokenKind.LowerId,
                                        text = "b",
                                        ..
                                    ):
                            state._cursor += 1
                        else:
                            throw(state.updateErrorCursor(state._cursor)),
                )
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        v.truncate(vLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let optionalCursor0 = state._cursor
            let symResult = try(
                ||:
                    if state.peek() is Option.Some(sym)
                            and sym is Token(kind = TokenKind.Comma, ..):
                        state._cursor += 1
                    else:
                        throw(state.updateErrorCursor(state._cursor))
                    (),
            )
            match symResult:
                Result.Err(err): state._cursor = optionalCursor0
                Result.Ok(ok): ()
            let value = do:
                v.len()
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


errorCursorBug(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            nodes.push(errorCursorBugAlt1(state))
            if state.peek().isNone():
                state._cursor
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.ErrorCursorBug, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            nodes.push(errorCursorBugAlt2(state))
            if state.peek().isNone():
                state._cursor
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(kind = NonTerminal.ErrorCursorBug, nodes)
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


errorCursorBugAlt1(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(
                    kind = NonTerminal.ErrorCursorBugAlt1,
                    nodes,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))


errorCursorBugAlt2(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        ||:
            let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let value = do:
                ParseTree.NonTerminal(
                    kind = NonTerminal.ErrorCursorBugAlt2,
                    nodes,
                )
            value,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(value): return value
    throw(state.updateErrorCursor(state._cursor))
