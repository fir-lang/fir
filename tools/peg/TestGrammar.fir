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

terminalA[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalA, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

terminalB[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalB, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

terminalAOrB[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalAOrB, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalAOrB, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

terminalAThenB[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalAThenB, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

zeroOrMoreAThenB[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                            nodes.push(ParseTree.Terminal(token))
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.ZeroOrMoreAThenB, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

oneOrMoreAThenB[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                            nodes.push(ParseTree.Terminal(token))
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.OneOrMoreAThenB, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

zeroOrOneAThenB[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            match iter.next():
                Option.Some((idx, token)):
                    if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                        nodes.push(ParseTree.Terminal(token))
                    else:
                        throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                Option.None:
                    throw(ParseError(cursor = U32.max()))
            curErr
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                nodes.truncate(nodesLen0)
            Result.Ok(newErr):
                curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.ZeroOrOneAThenB, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

ignoreAThenB[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IgnoreAThenB, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

ignoreAThenIgnoreB[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IgnoreAThenIgnoreB, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

ignoreGroupAThenB[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IgnoreGroupAThenB, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

nonTerminals[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = terminalAOrB(iter)
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = terminalAOrB(iter)
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminals, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

nonTerminalsBacktrack[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = terminalAOrB(iter)
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = terminalAOrB(iter)
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalsBacktrack, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalsBacktrack, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

negLookahead[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let symResult = try(||:
            match iter.next():
                Option.Some((idx, token)):
                    if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                        ()
                    else:
                        throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                Option.None:
                    throw(ParseError(cursor = U32.max()))
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(_):
                iter = iter0.clone()
                throw(ParseError.takeAdvanced(curErr, ParseError(cursor = iter0.clone().next[iter, (idx: U32, token: Token), ParseError]().unwrap().idx)))
        let nonTerminalResult = terminalAOrB(iter)
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NegLookahead, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

endOfInputTest[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    nodes.push(ParseTree.Terminal(token))
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next[iter, (idx: U32, token: Token), ParseError]():
            Option.Some((idx, token)):
                throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                U32.max()
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.EndOfInputTest, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

bracketedOneOrMoreA[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: ParseTree[Token, NonTerminal], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = oneOrMoreAThenB(iter)
                curErr = nonTerminalResult.newErr
                nodes.push(nonTerminalResult.tree)
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        match iter.next[iter, (idx: U32, token: Token), ParseError]():
            Option.Some((idx, token)):
                throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                U32.max()
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.BracketedOneOrMoreA, nodes)
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

semanticActionSimple[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Char, newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            'a'
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            'b'
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

semanticActionZeroOrMore[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Vec[Char], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let cs = Vec.empty()
        loop:
            let symResult = try(||:
                let nonTerminalResult = semanticActionSimple(iter)
                curErr = nonTerminalResult.newErr
                cs.push(nonTerminalResult.tree)
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        let value = do:
            cs
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

semanticActionOneOrMore[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Vec[Char], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let cs = Vec.empty()
        let nonTerminalResult = semanticActionSimple(iter)
        curErr = nonTerminalResult.newErr
        cs.push(nonTerminalResult.tree)
        loop:
            let symResult = try(||:
                let nonTerminalResult = semanticActionSimple(iter)
                curErr = nonTerminalResult.newErr
                cs.push(nonTerminalResult.tree)
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        let value = do:
            cs
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

semanticActionGroup[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Vec[Str], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    token
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    token
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let ab = (a = a, b = b)
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            let strs: Vec[Str] = Vec.[ab.a.text, ab.b.text]
            strs
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

semanticActionOptional[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Option[Token], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let symResult = try(||:
            match iter.next():
                Option.Some((idx, token)):
                    if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                        token
                    else:
                        throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                Option.None:
                    throw(ParseError(cursor = U32.max()))
            (err = curErr, val = cs)
        )
        let cs = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(newErr):
                curErr = ParseError.takeAdvancedOpt(curErr, newErr)
                Option.Some(ok.val)
        match iter.next[iter, (idx: U32, token: Token), ParseError]():
            Option.Some((idx, token)):
                throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                U32.max()
        let value = do:
            cs
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

semanticActionComplex[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: (aVec: Vec[Token], bVec: Vec[Token], cOpt: Option[Token]), newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let aVec = Vec.empty()
        loop:
            let symResult = try(||:
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                            aVec.push(token)
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        let bVec = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    bVec.push(token)
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        loop:
            let symResult = try(||:
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                            bVec.push(token)
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        let symResult = try(||:
            match iter.next():
                Option.Some((idx, token)):
                    if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                        token
                    else:
                        throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                Option.None:
                    throw(ParseError(cursor = U32.max()))
            (err = curErr, val = cOpt)
        )
        let cOpt = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(newErr):
                curErr = ParseError.takeAdvancedOpt(curErr, newErr)
                Option.Some(ok.val)
        let group = (aVec = aVec, bVec = bVec, cOpt = cOpt)
        match iter.next[iter, (idx: U32, token: Token), ParseError]():
            Option.Some((idx, token)):
                throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                U32.max()
        let value = do:
            group
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

cursorPositions[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Vec[U32], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let c0 = cursor
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let c1 = cursor
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let c2 = cursor
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let c3 = cursor
        let value = do:
            let vec: Vec[U32] = Vec.[c0, c1, c2, c3]
            vec
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

simpleGroup1[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Token, newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    token
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            x
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

simpleGroup2[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Option[Token], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let symResult = try(||:
            match iter.next():
                Option.Some((idx, token)):
                    if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                        token
                    else:
                        throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                Option.None:
                    throw(ParseError(cursor = U32.max()))
            (err = curErr, val = x)
        )
        let x = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(newErr):
                curErr = ParseError.takeAdvancedOpt(curErr, newErr)
                Option.Some(ok.val)
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            x
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

simpleGroup3[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Vec[Token], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let x = Vec.empty()
        loop:
            let symResult = try(||:
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                            x.push(token)
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            x
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

simpleGroup4[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Vec[Token], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let x = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    x.push(token)
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        loop:
            let symResult = try(||:
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                            x.push(token)
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            x
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

simpleGroup5[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Option[Token], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let symResult = try(||:
            match iter.next():
                Option.Some((idx, token)):
                    if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                        ()
                    else:
                        throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                Option.None:
                    throw(ParseError(cursor = U32.max()))
            match iter.next():
                Option.Some((idx, token)):
                    if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                        token
                    else:
                        throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                Option.None:
                    throw(ParseError(cursor = U32.max()))
            match iter.next():
                Option.Some((idx, token)):
                    if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                        ()
                    else:
                        throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                Option.None:
                    throw(ParseError(cursor = U32.max()))
            (err = curErr, val = x)
        )
        let x = match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                Option.None
            Result.Ok(newErr):
                curErr = ParseError.takeAdvancedOpt(curErr, newErr)
                Option.Some(ok.val)
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            x
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

simpleGroup6[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Vec[Token], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let x = Vec.empty()
        loop:
            let symResult = try(||:
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                            ()
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                            x.push(token)
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                            ()
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            x
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())

simpleGroup7[Iterator[iter, (idx: U32, token: Token), ParseError], Clone[iter]](iter: iter) (tree: Vec[Token], newErr: Option[ParseError]) / ParseError:
    let iter0 = iter.clone()
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let x = Vec.empty()
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                    x.push(token)
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        loop:
            let symResult = try(||:
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "a", ..):
                            ()
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "b", ..):
                            x.push(token)
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                match iter.next():
                    Option.Some((idx, token)):
                        if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                            ()
                        else:
                            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
                    Option.None:
                        throw(ParseError(cursor = U32.max()))
                curErr
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(newErr):
                    curErr = ParseError.takeAdvancedOpt(curErr, newErr)
        match iter.next():
            Option.Some((idx, token)):
                if token is Token(kind = TokenKind.LowerId, text = "c", ..):
                    ()
                else:
                    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = idx)))
            Option.None:
                throw(ParseError(cursor = U32.max()))
        let value = do:
            x
        (value = value, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            iter = iter0.clone()
        Result.Ok((value = value, err = newErr)):
            return (tree = value, newErr = newErr)
    throw(curErr.unwrap())
