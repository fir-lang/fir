# This is generated file, do not edit.

import ParseTree
import Token

type NonTerminal:
    TopDecl
    Type_
    RecordType
    VariantType
    FnType
    NamedType
    RecordTypeFields
    RecordTypeField
    VariantAlt
    FnArgTys
    ReturnType
    TypeDecl
    TypeParams
    TypeDeclRhs
    ConDecl
    NamedFields
    NamedField
    UnnamedFields
    InlineExpr
    InlineExprCont
    PrefixExpr
    Fields
    Args
    SimpleExpr
    UpperIdPath
    TyArgs
    ParenExpr
    ExprPrefix
    BinOp
    MatchAlt
    MatchRhs
    BlockExpr
    FnArgs
    FnRhs
    ReturnTy
    Pat
    SimplePat
    RecordPat
    ImportDecl

impl ToStr[NonTerminal]:
    toStr(self: NonTerminal) Str:
        match self:
            NonTerminal.TopDecl: "TopDecl"
            NonTerminal.Type_: "Type_"
            NonTerminal.RecordType: "RecordType"
            NonTerminal.VariantType: "VariantType"
            NonTerminal.FnType: "FnType"
            NonTerminal.NamedType: "NamedType"
            NonTerminal.RecordTypeFields: "RecordTypeFields"
            NonTerminal.RecordTypeField: "RecordTypeField"
            NonTerminal.VariantAlt: "VariantAlt"
            NonTerminal.FnArgTys: "FnArgTys"
            NonTerminal.ReturnType: "ReturnType"
            NonTerminal.TypeDecl: "TypeDecl"
            NonTerminal.TypeParams: "TypeParams"
            NonTerminal.TypeDeclRhs: "TypeDeclRhs"
            NonTerminal.ConDecl: "ConDecl"
            NonTerminal.NamedFields: "NamedFields"
            NonTerminal.NamedField: "NamedField"
            NonTerminal.UnnamedFields: "UnnamedFields"
            NonTerminal.InlineExpr: "InlineExpr"
            NonTerminal.InlineExprCont: "InlineExprCont"
            NonTerminal.PrefixExpr: "PrefixExpr"
            NonTerminal.Fields: "Fields"
            NonTerminal.Args: "Args"
            NonTerminal.SimpleExpr: "SimpleExpr"
            NonTerminal.UpperIdPath: "UpperIdPath"
            NonTerminal.TyArgs: "TyArgs"
            NonTerminal.ParenExpr: "ParenExpr"
            NonTerminal.ExprPrefix: "ExprPrefix"
            NonTerminal.BinOp: "BinOp"
            NonTerminal.MatchAlt: "MatchAlt"
            NonTerminal.MatchRhs: "MatchRhs"
            NonTerminal.BlockExpr: "BlockExpr"
            NonTerminal.FnArgs: "FnArgs"
            NonTerminal.FnRhs: "FnRhs"
            NonTerminal.ReturnTy: "ReturnTy"
            NonTerminal.Pat: "Pat"
            NonTerminal.SimplePat: "SimplePat"
            NonTerminal.RecordPat: "RecordPat"
            NonTerminal.ImportDecl: "ImportDecl"

impl Eq[NonTerminal]:
    __eq(self: NonTerminal, other: NonTerminal) Bool:
        match (left = self, right = other):
            (left = NonTerminal.TopDecl, right = NonTerminal.TopDecl): Bool.True
            (left = NonTerminal.Type_, right = NonTerminal.Type_): Bool.True
            (left = NonTerminal.RecordType, right = NonTerminal.RecordType): Bool.True
            (left = NonTerminal.VariantType, right = NonTerminal.VariantType): Bool.True
            (left = NonTerminal.FnType, right = NonTerminal.FnType): Bool.True
            (left = NonTerminal.NamedType, right = NonTerminal.NamedType): Bool.True
            (left = NonTerminal.RecordTypeFields, right = NonTerminal.RecordTypeFields): Bool.True
            (left = NonTerminal.RecordTypeField, right = NonTerminal.RecordTypeField): Bool.True
            (left = NonTerminal.VariantAlt, right = NonTerminal.VariantAlt): Bool.True
            (left = NonTerminal.FnArgTys, right = NonTerminal.FnArgTys): Bool.True
            (left = NonTerminal.ReturnType, right = NonTerminal.ReturnType): Bool.True
            (left = NonTerminal.TypeDecl, right = NonTerminal.TypeDecl): Bool.True
            (left = NonTerminal.TypeParams, right = NonTerminal.TypeParams): Bool.True
            (left = NonTerminal.TypeDeclRhs, right = NonTerminal.TypeDeclRhs): Bool.True
            (left = NonTerminal.ConDecl, right = NonTerminal.ConDecl): Bool.True
            (left = NonTerminal.NamedFields, right = NonTerminal.NamedFields): Bool.True
            (left = NonTerminal.NamedField, right = NonTerminal.NamedField): Bool.True
            (left = NonTerminal.UnnamedFields, right = NonTerminal.UnnamedFields): Bool.True
            (left = NonTerminal.InlineExpr, right = NonTerminal.InlineExpr): Bool.True
            (left = NonTerminal.InlineExprCont, right = NonTerminal.InlineExprCont): Bool.True
            (left = NonTerminal.PrefixExpr, right = NonTerminal.PrefixExpr): Bool.True
            (left = NonTerminal.Fields, right = NonTerminal.Fields): Bool.True
            (left = NonTerminal.Args, right = NonTerminal.Args): Bool.True
            (left = NonTerminal.SimpleExpr, right = NonTerminal.SimpleExpr): Bool.True
            (left = NonTerminal.UpperIdPath, right = NonTerminal.UpperIdPath): Bool.True
            (left = NonTerminal.TyArgs, right = NonTerminal.TyArgs): Bool.True
            (left = NonTerminal.ParenExpr, right = NonTerminal.ParenExpr): Bool.True
            (left = NonTerminal.ExprPrefix, right = NonTerminal.ExprPrefix): Bool.True
            (left = NonTerminal.BinOp, right = NonTerminal.BinOp): Bool.True
            (left = NonTerminal.MatchAlt, right = NonTerminal.MatchAlt): Bool.True
            (left = NonTerminal.MatchRhs, right = NonTerminal.MatchRhs): Bool.True
            (left = NonTerminal.BlockExpr, right = NonTerminal.BlockExpr): Bool.True
            (left = NonTerminal.FnArgs, right = NonTerminal.FnArgs): Bool.True
            (left = NonTerminal.FnRhs, right = NonTerminal.FnRhs): Bool.True
            (left = NonTerminal.ReturnTy, right = NonTerminal.ReturnTy): Bool.True
            (left = NonTerminal.Pat, right = NonTerminal.Pat): Bool.True
            (left = NonTerminal.SimplePat, right = NonTerminal.SimplePat): Bool.True
            (left = NonTerminal.RecordPat, right = NonTerminal.RecordPat): Bool.True
            (left = NonTerminal.ImportDecl, right = NonTerminal.ImportDecl): Bool.True
            _: Bool.False

topDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = typeDecl(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TopDecl, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = importDecl(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TopDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

type_(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = namedType(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = recordType(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = variantType(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = fnType(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

recordType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = recordTypeFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

variantType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = variantAlt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = variantAlt(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = variantAlt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = variantAlt(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

fnType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperFn, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = fnArgTys(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = returnType(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FnType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

namedType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = type_(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

recordTypeFields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = recordTypeField(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeFields, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = recordTypeField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = recordTypeField(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeFields, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

recordTypeField(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

variantAlt(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = recordTypeFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantAlt, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantAlt, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

fnArgTys(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FnArgTys, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

returnType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ReturnType, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

typeDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Type, ..):
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = typeDeclRhs(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDecl, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Type, ..):
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDecl, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Prim, ..):
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
        if tokens.get(cursor) is Token(kind = TokenKind.Type, ..):
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

typeParams(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeParams, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeParams, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

typeDeclRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = conDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = conDecl(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDeclRhs, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = namedField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = namedField(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TypeDeclRhs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

conDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = namedFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ConDecl, nodes), newCursor = newCursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = unnamedFields(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ConDecl, nodes), newCursor = newCursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ConDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

namedFields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = namedField(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = namedField(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedFields, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

namedField(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.NamedField, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

unnamedFields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.UnnamedFields, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

inlineExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = prefixExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = inlineExprCont(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

inlineExprCont(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = binOp(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = prefixExpr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineExprCont, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Is, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = pat(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.InlineExprCont, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

prefixExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.PrefixExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

fields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
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
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
                if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Fields, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

args(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Args, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

simpleExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Match, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = simpleExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = matchAlt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = matchAlt(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.If, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = simpleExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = blockExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
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
                if tokens.get(cursor) is Token(kind = TokenKind.Elif, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = simpleExpr(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = blockExpr(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Else, ..):
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
            if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
                cursor += 1
            else:
                throw(
                    ParseError.UnexpectedToken(
                        token = tokens.get(cursor),
                        cursor = cursor,
                    ))
            let nonTerminalResult = blockExpr(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Do, ..):
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
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = blockExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Pipe, ..):
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
            let nonTerminalResult = fnArgs(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Pipe, ..):
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
            let nonTerminalResult = returnTy(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = fnRhs(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.PipePipe, ..):
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
            let nonTerminalResult = returnTy(tokens, cursor)
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = fnRhs(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Int, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.HexInt, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.BinInt, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

upperIdPath(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.UpperIdPath, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.TildeUpperId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.UpperIdPath, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

tyArgs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TyArgs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

parenExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ParenExpr, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ParenExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

exprPrefix(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ExprPrefix, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ExprPrefix, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

binOp(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.BinOp, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.BinOp, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.BinOp, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.BinOp, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.EqEq, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.BinOp, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

matchAlt(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = pat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = matchRhs(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.MatchAlt, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

matchRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = blockExpr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.MatchRhs, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = simpleExpr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.MatchRhs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

blockExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
                let nonTerminalResult = inlineExpr(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.BlockExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

fnArgs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = type_(tokens, cursor)
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
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
                if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FnArgs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

fnRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                ))
        let nonTerminalResult = blockExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FnRhs, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FnRhs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

returnTy(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
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
        let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ReturnTy, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ReturnTy, nodes), newCursor = newCursor)
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
        let nonTerminalResult = type_(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ReturnTy, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

pat(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        let nonTerminalResult = simplePat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Pipe, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(
                        ParseError.UnexpectedToken(
                            token = tokens.get(cursor),
                            cursor = cursor,
                        ))
                let nonTerminalResult = simplePat(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Pat, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

simplePat(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimplePat, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = upperIdPath(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimplePat, nodes), newCursor = newCursor)
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
            let nonTerminalResult = recordPat(tokens, cursor)
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
                    let nonTerminalResult = recordPat(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimplePat, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Underscore, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimplePat, nodes), newCursor = newCursor)
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimplePat, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimplePat, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

recordPat(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
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
        let nonTerminalResult = pat(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordPat, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = pat(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordPat, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))

importDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError[Token]:
    let cursor0 = cursor
    let curErr: Option[ParseError[Token]] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Import, ..):
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ImportDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(
                    token = tokens.get(cursor),
                    cursor = cursor,
                )))
