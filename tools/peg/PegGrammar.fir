# This is generated file, do not edit.

import Compiler.Token
import Peg.ParseTree

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
    NonTerminalRhs
    InlineTokenTree
    InlineTokenTreeSingle
    InlineTokenTreeTerminator
    IndentedTokenTree
    IndentedTokenTreeSingle
    IndentedTokenTreeTerminator
    Type_
    RecordType
    RecordTypeStart
    RecordTypeCont
    VariantType
    VariantTypeStart
    VariantTypeCont
    FnType
    NamedType
    RecordTypeFields
    RecordTypeField
    VariantAlt
    FnArgTys
    ReturnTy

impl ToStr[NonTerminal]:
    toStr(self: NonTerminal) Str:
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
            NonTerminal.NonTerminalRhs: "NonTerminalRhs"
            NonTerminal.InlineTokenTree: "InlineTokenTree"
            NonTerminal.InlineTokenTreeSingle: "InlineTokenTreeSingle"
            NonTerminal.InlineTokenTreeTerminator: "InlineTokenTreeTerminator"
            NonTerminal.IndentedTokenTree: "IndentedTokenTree"
            NonTerminal.IndentedTokenTreeSingle: "IndentedTokenTreeSingle"
            NonTerminal.IndentedTokenTreeTerminator: "IndentedTokenTreeTerminator"
            NonTerminal.Type_: "Type_"
            NonTerminal.RecordType: "RecordType"
            NonTerminal.RecordTypeStart: "RecordTypeStart"
            NonTerminal.RecordTypeCont: "RecordTypeCont"
            NonTerminal.VariantType: "VariantType"
            NonTerminal.VariantTypeStart: "VariantTypeStart"
            NonTerminal.VariantTypeCont: "VariantTypeCont"
            NonTerminal.FnType: "FnType"
            NonTerminal.NamedType: "NamedType"
            NonTerminal.RecordTypeFields: "RecordTypeFields"
            NonTerminal.RecordTypeField: "RecordTypeField"
            NonTerminal.VariantAlt: "VariantAlt"
            NonTerminal.FnArgTys: "FnArgTys"
            NonTerminal.ReturnTy: "ReturnTy"

impl Eq[NonTerminal]:
    __eq(self: NonTerminal, other: NonTerminal) Bool:
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
            (left = NonTerminal.NonTerminalRhs, right = NonTerminal.NonTerminalRhs): Bool.True
            (left = NonTerminal.InlineTokenTree, right = NonTerminal.InlineTokenTree): Bool.True
            (left = NonTerminal.InlineTokenTreeSingle, right = NonTerminal.InlineTokenTreeSingle): Bool.True
            (left = NonTerminal.InlineTokenTreeTerminator, right = NonTerminal.InlineTokenTreeTerminator): Bool.True
            (left = NonTerminal.IndentedTokenTree, right = NonTerminal.IndentedTokenTree): Bool.True
            (left = NonTerminal.IndentedTokenTreeSingle, right = NonTerminal.IndentedTokenTreeSingle): Bool.True
            (left = NonTerminal.IndentedTokenTreeTerminator, right = NonTerminal.IndentedTokenTreeTerminator): Bool.True
            (left = NonTerminal.Type_, right = NonTerminal.Type_): Bool.True
            (left = NonTerminal.RecordType, right = NonTerminal.RecordType): Bool.True
            (left = NonTerminal.RecordTypeStart, right = NonTerminal.RecordTypeStart): Bool.True
            (left = NonTerminal.RecordTypeCont, right = NonTerminal.RecordTypeCont): Bool.True
            (left = NonTerminal.VariantType, right = NonTerminal.VariantType): Bool.True
            (left = NonTerminal.VariantTypeStart, right = NonTerminal.VariantTypeStart): Bool.True
            (left = NonTerminal.VariantTypeCont, right = NonTerminal.VariantTypeCont): Bool.True
            (left = NonTerminal.FnType, right = NonTerminal.FnType): Bool.True
            (left = NonTerminal.NamedType, right = NonTerminal.NamedType): Bool.True
            (left = NonTerminal.RecordTypeFields, right = NonTerminal.RecordTypeFields): Bool.True
            (left = NonTerminal.RecordTypeField, right = NonTerminal.RecordTypeField): Bool.True
            (left = NonTerminal.VariantAlt, right = NonTerminal.VariantAlt): Bool.True
            (left = NonTerminal.FnArgTys, right = NonTerminal.FnArgTys): Bool.True
            (left = NonTerminal.ReturnTy, right = NonTerminal.ReturnTy): Bool.True
            _: Bool.False

grammar(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = importDecls(state)
        nodes.push(nonTerminalResult)
        let nonTerminalResult = typeDecls(state)
        nodes.push(nonTerminalResult)
        let nonTerminalResult = terminalsDecl(state)
        nodes.push(nonTerminalResult)
        let nonTerminalResult = nonTerminalDecls(state)
        nodes.push(nonTerminalResult)
        if state.peek().isNone():
            state._cursor
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.Grammar, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

importDecls(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = importDecl(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.ImportDecls, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

importDecl(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Import, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Dot, ..):
                    state._cursor += 1
                else:
                    throw(state._cursor)
                if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.UpperId, ..):
                    nodes.push(ParseTree.Terminal(sym))
                    state._cursor += 1
                else:
                    throw(state._cursor)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.ImportDecl, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

typeDecls(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = typeDecl(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TypeDecls, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

typeDecl(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Type, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Eq, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TypeDecl, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

terminalsDecl(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.UpperId, text = "Terminals", ..):
                state._cursor += 1
            else:
                throw(state._cursor)
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Colon, ..):
                state._cursor += 1
            else:
                throw(state._cursor)
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state._cursor)
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Indent, ..):
                state._cursor += 1
            else:
                throw(state._cursor)
            let nonTerminalResult = terminalDecl(state)
            nodes.push(nonTerminalResult)
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let nodesLen0 = nodes.len()
                let symResult = try(||:
                    let nonTerminalResult = terminalDecl(state)
                    nodes.push(nonTerminalResult)
                )
                match symResult:
                    Result.Err(err):
                        state.updateErrorCursor(err)
                        state._cursor = zeroOrMoreCursor0
                        nodes.truncate(nodesLen0)
                        break
                    Result.Ok(ok):
                        zeroOrMoreCursor0 = state._cursor
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Dedent, ..):
                state._cursor += 1
            else:
                throw(state._cursor)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalsDecl, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

terminalDecl(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Str, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Eq, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let state0 = state.clone()
        let symResult = try(||:
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
                state._cursor += 1
            else:
                throw(state._cursor)
        )
        match symResult:
            Result.Err(err):
                state.cloneFrom(state0)
            Result.Ok(_):
                state.cloneFrom(state0)
                throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let state0 = state.clone()
                let symResult = try(||:
                    if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
                        state._cursor += 1
                    else:
                        throw(state._cursor)
                )
                match symResult:
                    Result.Err(err):
                        state.cloneFrom(state0)
                    Result.Ok(_):
                        state.cloneFrom(state0)
                        throw(state._cursor)
                if state.peek() is Option.Some(sym) and sym is Token(..):
                    nodes.push(ParseTree.Terminal(sym))
                    state._cursor += 1
                else:
                    throw(state._cursor)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalDecl, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

nonTerminalDecls(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = nonTerminalDecl(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalDecls, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

nonTerminalDecl(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = type_(state)
            nodes.push(nonTerminalResult)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Colon, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Indent, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = nonTerminalAlt(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = nonTerminalAlt(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Dedent, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalDecl, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

nonTerminalAlt(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = symbol(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = symbol(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let nonTerminalResult = nonTerminalRhs(state)
        nodes.push(nonTerminalResult)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalAlt, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

symbol(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = symbolPrefix(state)
            nodes.push(nonTerminalResult)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        let nonTerminalResult = symbolNonRec(state)
        nodes.push(nonTerminalResult)
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = symbolSuffix(state)
            nodes.push(nonTerminalResult)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.Symbol, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Dollar, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.Symbol, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

symbolPrefix(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Minus, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Underscore, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Eq, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

symbolNonRec(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.SymbolNonRec, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Str, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.SymbolNonRec, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LParen, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = symbol(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = symbol(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.SymbolNonRec, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Caret, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.SymbolNonRec, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

symbolSuffix(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Star, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.SymbolSuffix, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Plus, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.SymbolSuffix, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Question, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.SymbolSuffix, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

nonTerminalRhs(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalRhs, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Colon, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = inlineTokenTreeSingle(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = inlineTokenTreeSingle(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalRhs, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Colon, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Indent, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTreeSingle(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = indentedTokenTreeSingle(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Dedent, ..):
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalRhs, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

inlineTokenTree(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = inlineTokenTreeSingle(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTree, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

inlineTokenTreeSingle(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LParenRow, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LBracketRow, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LBrace, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBrace, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Indent, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Dedent, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let state0 = state.clone()
        let symResult = try(||:
            let nonTerminalResult = inlineTokenTreeTerminator(state)
        )
        match symResult:
            Result.Err(err):
                state.cloneFrom(state0)
            Result.Ok(_):
                state.cloneFrom(state0)
                throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

inlineTokenTreeTerminator(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeTerminator, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeTerminator, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBrace, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeTerminator, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Dedent, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeTerminator, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Newline, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeTerminator, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

indentedTokenTree(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = indentedTokenTreeSingle(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTree, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

indentedTokenTreeSingle(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LParenRow, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LBracketRow, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LBrace, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBrace, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Indent, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = indentedTokenTree(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Dedent, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let state0 = state.clone()
        let symResult = try(||:
            let nonTerminalResult = indentedTokenTreeTerminator(state)
        )
        match symResult:
            Result.Err(err):
                state.cloneFrom(state0)
            Result.Ok(_):
                state.cloneFrom(state0)
                throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

indentedTokenTreeTerminator(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeTerminator, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeTerminator, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBrace, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeTerminator, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Dedent, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeTerminator, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

type_(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = namedType(state)
        nodes.push(nonTerminalResult)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = recordType(state)
        nodes.push(nonTerminalResult)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = variantType(state)
        nodes.push(nonTerminalResult)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = fnType(state)
        nodes.push(nonTerminalResult)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

recordType(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = recordTypeStart(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = recordTypeStart(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.DotDot, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = recordTypeStart(state)
        nodes.push(nonTerminalResult)
        let nonTerminalResult = recordTypeField(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
                    nodes.push(ParseTree.Terminal(sym))
                    state._cursor += 1
                else:
                    throw(state._cursor)
                let nonTerminalResult = recordTypeField(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = recordTypeCont(state)
            nodes.push(nonTerminalResult)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

recordTypeStart(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordTypeStart, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LParenRow, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordTypeStart, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

recordTypeCont(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.DotDot, ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state._cursor)
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LowerId, ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state._cursor)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordTypeCont, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

variantType(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = variantTypeStart(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = variantTypeStart(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.DotDot, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = variantTypeStart(state)
        nodes.push(nonTerminalResult)
        let nonTerminalResult = variantAlt(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
                    nodes.push(ParseTree.Terminal(sym))
                    state._cursor += 1
                else:
                    throw(state._cursor)
                let nonTerminalResult = variantAlt(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = variantTypeCont(state)
            nodes.push(nonTerminalResult)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

variantTypeStart(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.VariantTypeStart, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LBracketRow, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.VariantTypeStart, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

variantTypeCont(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.DotDot, ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state._cursor)
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LowerId, ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state._cursor)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.VariantTypeCont, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

fnType(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.UpperFn, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = fnArgTys(state)
            nodes.push(nonTerminalResult)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = returnTy(state)
            nodes.push(nonTerminalResult)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.FnType, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

namedType(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = type_(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
                    nodes.push(ParseTree.Terminal(sym))
                    state._cursor += 1
                else:
                    throw(state._cursor)
                let nonTerminalResult = type_(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state._cursor)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

recordTypeFields(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = recordTypeField(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
                    nodes.push(ParseTree.Terminal(sym))
                    state._cursor += 1
                else:
                    throw(state._cursor)
                let nonTerminalResult = recordTypeField(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.DotDot, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordTypeFields, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = recordTypeField(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
                    nodes.push(ParseTree.Terminal(sym))
                    state._cursor += 1
                else:
                    throw(state._cursor)
                let nonTerminalResult = recordTypeField(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state._cursor)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordTypeFields, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

recordTypeField(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Colon, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = type_(state)
        nodes.push(nonTerminalResult)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = type_(state)
        nodes.push(nonTerminalResult)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

variantAlt(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = recordTypeFields(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.VariantAlt, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.VariantAlt, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

fnArgTys(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = type_(state)
        nodes.push(nonTerminalResult)
        let zeroOrMoreCursor0 = state._cursor
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
                    nodes.push(ParseTree.Terminal(sym))
                    state._cursor += 1
                else:
                    throw(state._cursor)
                let nonTerminalResult = type_(state)
                nodes.push(nonTerminalResult)
            )
            match symResult:
                Result.Err(err):
                    state.updateErrorCursor(err)
                    state._cursor = zeroOrMoreCursor0
                    nodes.truncate(nodesLen0)
                    break
                Result.Ok(ok):
                    zeroOrMoreCursor0 = state._cursor
        let optionalCursor0 = state._cursor
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Comma, ..):
                nodes.push(ParseTree.Terminal(sym))
                state._cursor += 1
            else:
                throw(state._cursor)
            ()
        )
        match symResult:
            Result.Err(err):
                state._cursor = optionalCursor0
                state.updateErrorCursor(err)
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                ()
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.FnArgTys, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)

returnTy(state: ParserState[Token]) ParseTree[Token, NonTerminal] / U32:
    let cursor0 = state._cursor
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = type_(state)
        nodes.push(nonTerminalResult)
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Slash, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = type_(state)
        nodes.push(nonTerminalResult)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.ReturnTy, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        let nonTerminalResult = type_(state)
        nodes.push(nonTerminalResult)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.ReturnTy, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    let altResult = try(||:
        let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
        if state.peek() is Option.Some(sym) and sym is Token(kind = TokenKind.Slash, ..):
            nodes.push(ParseTree.Terminal(sym))
            state._cursor += 1
        else:
            throw(state._cursor)
        let nonTerminalResult = type_(state)
        nodes.push(nonTerminalResult)
        let value = do:
            ParseTree.NonTerminal(kind = NonTerminal.ReturnTy, nodes)
        value
    )
    match altResult:
        Result.Err(err):
            state.updateErrorCursor(err)
            state._cursor = cursor0
        Result.Ok(value):
            return value
    throw(state._cursor)
