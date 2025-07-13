# This is generated file, do not edit.

import Compiler.Token
import ParseTree

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

grammar(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = importDecls(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = typeDecls(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = terminalsDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = nonTerminalDecls(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Grammar, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

importDecls(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = importDecl(tokens, cursor)
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
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ImportDecls, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

importDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Import, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dot, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ImportDecl, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

typeDecls(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = typeDecl(tokens, cursor)
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
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDecls, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

typeDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Type, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Eq, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDecl, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

terminalsDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, text = "Terminals", ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            let nonTerminalResult = terminalDecl(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            nodes.push(nonTerminalResult.tree)
            loop:
                let nodesLen0 = nodes.len()
                let symResult = try(||:
                    let nonTerminalResult = terminalDecl(tokens, cursor)
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
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
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
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TerminalsDecl, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

terminalDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Str, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Eq, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let tokensLen0 = tokens.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
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
        if tokens.getOpt(cursor) is Option.Some(Token(..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let tokensLen0 = tokens.len()
                let symResult = try(||:
                    if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
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
                if tokens.getOpt(cursor) is Option.Some(Token(..)):
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TerminalDecl, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

nonTerminalDecls(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = nonTerminalDecl(tokens, cursor)
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
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalDecls, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

nonTerminalDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = type_(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            nodes.push(nonTerminalResult.tree)
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = nonTerminalAlt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = nonTerminalAlt(tokens, cursor)
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalDecl, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

nonTerminalAlt(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = symbol(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = symbol(tokens, cursor)
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
        let nonTerminalResult = nonTerminalRhs(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalAlt, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

symbol(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = symbolPrefix(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            nodes.push(nonTerminalResult.tree)
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let nonTerminalResult = symbolNonRec(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = symbolSuffix(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            nodes.push(nonTerminalResult.tree)
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Symbol, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dollar, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Symbol, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

symbolPrefix(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Minus, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Underscore, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Eq, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

symbolNonRec(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolNonRec, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Str, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolNonRec, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = symbol(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = symbol(tokens, cursor)
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolNonRec, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

symbolSuffix(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Star, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolSuffix, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Plus, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolSuffix, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Question, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SymbolSuffix, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

nonTerminalRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalRhs, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = inlineTokenTreeSingle(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = inlineTokenTreeSingle(tokens, cursor)
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalRhs, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTreeSingle(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = indentedTokenTreeSingle(tokens, cursor)
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NonTerminalRhs, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

inlineTokenTree(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = inlineTokenTreeSingle(tokens, cursor)
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
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTree, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

inlineTokenTreeSingle(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParenRow, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracketRow, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBrace, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBrace, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let tokensLen0 = tokens.len()
        let symResult = try(||:
            let nonTerminalResult = inlineTokenTreeTerminator(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                tokens.truncate(tokensLen0)
            Result.Ok(_):
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

inlineTokenTreeTerminator(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeTerminator, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeTerminator, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBrace, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeTerminator, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeTerminator, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Newline, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineTokenTreeTerminator, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

indentedTokenTree(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = indentedTokenTreeSingle(tokens, cursor)
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
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTree, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

indentedTokenTreeSingle(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParenRow, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracketRow, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBrace, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBrace, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Indent, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = indentedTokenTree(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let tokensLen0 = tokens.len()
        let symResult = try(||:
            let nonTerminalResult = indentedTokenTreeTerminator(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                tokens.truncate(tokensLen0)
            Result.Ok(_):
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeSingle, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

indentedTokenTreeTerminator(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeTerminator, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeTerminator, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBrace, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeTerminator, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Dedent, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.IndentedTokenTreeTerminator, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

type_(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = namedType(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = recordType(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = variantType(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = fnType(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = recordTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = recordTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = recordTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = recordTypeField(tokens, cursor)
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = recordTypeCont(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            nodes.push(nonTerminalResult.tree)
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordTypeStart(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeStart, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParenRow, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeStart, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordTypeCont(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
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
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeCont, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

variantType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = variantTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = variantTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = variantTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = variantAlt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = variantAlt(tokens, cursor)
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = variantTypeCont(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            nodes.push(nonTerminalResult.tree)
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

variantTypeStart(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantTypeStart, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracketRow, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantTypeStart, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

variantTypeCont(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
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
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantTypeCont, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

fnType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperFn, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = fnArgTys(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            nodes.push(nonTerminalResult.tree)
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = returnTy(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            curErr = nonTerminalResult.newErr
            nodes.push(nonTerminalResult.tree)
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                nodes.truncate(nodesLen0)
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FnType, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

namedType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = type_(tokens, cursor)
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordTypeFields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = recordTypeField(tokens, cursor)
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
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.DotDot, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeFields, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = recordTypeField(tokens, cursor)
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
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
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeFields, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

recordTypeField(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Colon, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

variantAlt(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LParen, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = recordTypeFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RParen, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantAlt, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantAlt, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

fnArgTys(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = type_(tokens, cursor)
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
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
        (cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
            nodes.clear()
        Result.Ok((cursor = newCursor, err = newErr)):
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FnArgTys, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

returnTy(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        nodes.push(nonTerminalResult.tree)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Slash, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ReturnTy, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ReturnTy, nodes), newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Slash, ..)):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ReturnTy, nodes), newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
