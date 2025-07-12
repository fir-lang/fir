# This is generated file, do not edit.

import Peg.ParseTree
import Token

type NonTerminal:
    Module
    TopDecl
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
    TypeDecl
    TypeParams
    TypeDeclRhs
    ConDecl
    NamedFields
    NamedField
    UnnamedFields
    Expr
    InlineExpr
    BlockExpr
    InlineExprCont
    PrefixExpr
    ExprSuffix
    Field
    Args
    Arg
    SimpleExpr
    Sequence
    SeqElem
    UpperIdPath
    TyArgs
    ParenExpr
    ExprPrefix
    BinOp
    MatchAlt
    AltGuard
    MatchRhs
    FnArgs
    ReturnTy
    Stmt
    LoopLabel
    LetRhs
    StmtExprCont
    AssignOp
    Pat
    SimplePat
    StrPfxBinder
    RecordFieldPat
    ImportDecl
    TopFunDecl
    TopFunSig
    ParentTy
    Context
    ParamList
    Param
    TraitDecl
    TraitDeclRhs
    FunSig
    ImplDecl
    ImplDeclRhs
    FunDecl
    FunDeclRhs

impl ToStr[NonTerminal]:
    toStr(self: NonTerminal) Str:
        match self:
            NonTerminal.Module: "Module"
            NonTerminal.TopDecl: "TopDecl"
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
            NonTerminal.TypeDecl: "TypeDecl"
            NonTerminal.TypeParams: "TypeParams"
            NonTerminal.TypeDeclRhs: "TypeDeclRhs"
            NonTerminal.ConDecl: "ConDecl"
            NonTerminal.NamedFields: "NamedFields"
            NonTerminal.NamedField: "NamedField"
            NonTerminal.UnnamedFields: "UnnamedFields"
            NonTerminal.Expr: "Expr"
            NonTerminal.InlineExpr: "InlineExpr"
            NonTerminal.BlockExpr: "BlockExpr"
            NonTerminal.InlineExprCont: "InlineExprCont"
            NonTerminal.PrefixExpr: "PrefixExpr"
            NonTerminal.ExprSuffix: "ExprSuffix"
            NonTerminal.Field: "Field"
            NonTerminal.Args: "Args"
            NonTerminal.Arg: "Arg"
            NonTerminal.SimpleExpr: "SimpleExpr"
            NonTerminal.Sequence: "Sequence"
            NonTerminal.SeqElem: "SeqElem"
            NonTerminal.UpperIdPath: "UpperIdPath"
            NonTerminal.TyArgs: "TyArgs"
            NonTerminal.ParenExpr: "ParenExpr"
            NonTerminal.ExprPrefix: "ExprPrefix"
            NonTerminal.BinOp: "BinOp"
            NonTerminal.MatchAlt: "MatchAlt"
            NonTerminal.AltGuard: "AltGuard"
            NonTerminal.MatchRhs: "MatchRhs"
            NonTerminal.FnArgs: "FnArgs"
            NonTerminal.ReturnTy: "ReturnTy"
            NonTerminal.Stmt: "Stmt"
            NonTerminal.LoopLabel: "LoopLabel"
            NonTerminal.LetRhs: "LetRhs"
            NonTerminal.StmtExprCont: "StmtExprCont"
            NonTerminal.AssignOp: "AssignOp"
            NonTerminal.Pat: "Pat"
            NonTerminal.SimplePat: "SimplePat"
            NonTerminal.StrPfxBinder: "StrPfxBinder"
            NonTerminal.RecordFieldPat: "RecordFieldPat"
            NonTerminal.ImportDecl: "ImportDecl"
            NonTerminal.TopFunDecl: "TopFunDecl"
            NonTerminal.TopFunSig: "TopFunSig"
            NonTerminal.ParentTy: "ParentTy"
            NonTerminal.Context: "Context"
            NonTerminal.ParamList: "ParamList"
            NonTerminal.Param: "Param"
            NonTerminal.TraitDecl: "TraitDecl"
            NonTerminal.TraitDeclRhs: "TraitDeclRhs"
            NonTerminal.FunSig: "FunSig"
            NonTerminal.ImplDecl: "ImplDecl"
            NonTerminal.ImplDeclRhs: "ImplDeclRhs"
            NonTerminal.FunDecl: "FunDecl"
            NonTerminal.FunDeclRhs: "FunDeclRhs"

impl Eq[NonTerminal]:
    __eq(self: NonTerminal, other: NonTerminal) Bool:
        match (left = self, right = other):
            (left = NonTerminal.Module, right = NonTerminal.Module): Bool.True
            (left = NonTerminal.TopDecl, right = NonTerminal.TopDecl): Bool.True
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
            (left = NonTerminal.TypeDecl, right = NonTerminal.TypeDecl): Bool.True
            (left = NonTerminal.TypeParams, right = NonTerminal.TypeParams): Bool.True
            (left = NonTerminal.TypeDeclRhs, right = NonTerminal.TypeDeclRhs): Bool.True
            (left = NonTerminal.ConDecl, right = NonTerminal.ConDecl): Bool.True
            (left = NonTerminal.NamedFields, right = NonTerminal.NamedFields): Bool.True
            (left = NonTerminal.NamedField, right = NonTerminal.NamedField): Bool.True
            (left = NonTerminal.UnnamedFields, right = NonTerminal.UnnamedFields): Bool.True
            (left = NonTerminal.Expr, right = NonTerminal.Expr): Bool.True
            (left = NonTerminal.InlineExpr, right = NonTerminal.InlineExpr): Bool.True
            (left = NonTerminal.BlockExpr, right = NonTerminal.BlockExpr): Bool.True
            (left = NonTerminal.InlineExprCont, right = NonTerminal.InlineExprCont): Bool.True
            (left = NonTerminal.PrefixExpr, right = NonTerminal.PrefixExpr): Bool.True
            (left = NonTerminal.ExprSuffix, right = NonTerminal.ExprSuffix): Bool.True
            (left = NonTerminal.Field, right = NonTerminal.Field): Bool.True
            (left = NonTerminal.Args, right = NonTerminal.Args): Bool.True
            (left = NonTerminal.Arg, right = NonTerminal.Arg): Bool.True
            (left = NonTerminal.SimpleExpr, right = NonTerminal.SimpleExpr): Bool.True
            (left = NonTerminal.Sequence, right = NonTerminal.Sequence): Bool.True
            (left = NonTerminal.SeqElem, right = NonTerminal.SeqElem): Bool.True
            (left = NonTerminal.UpperIdPath, right = NonTerminal.UpperIdPath): Bool.True
            (left = NonTerminal.TyArgs, right = NonTerminal.TyArgs): Bool.True
            (left = NonTerminal.ParenExpr, right = NonTerminal.ParenExpr): Bool.True
            (left = NonTerminal.ExprPrefix, right = NonTerminal.ExprPrefix): Bool.True
            (left = NonTerminal.BinOp, right = NonTerminal.BinOp): Bool.True
            (left = NonTerminal.MatchAlt, right = NonTerminal.MatchAlt): Bool.True
            (left = NonTerminal.AltGuard, right = NonTerminal.AltGuard): Bool.True
            (left = NonTerminal.MatchRhs, right = NonTerminal.MatchRhs): Bool.True
            (left = NonTerminal.FnArgs, right = NonTerminal.FnArgs): Bool.True
            (left = NonTerminal.ReturnTy, right = NonTerminal.ReturnTy): Bool.True
            (left = NonTerminal.Stmt, right = NonTerminal.Stmt): Bool.True
            (left = NonTerminal.LoopLabel, right = NonTerminal.LoopLabel): Bool.True
            (left = NonTerminal.LetRhs, right = NonTerminal.LetRhs): Bool.True
            (left = NonTerminal.StmtExprCont, right = NonTerminal.StmtExprCont): Bool.True
            (left = NonTerminal.AssignOp, right = NonTerminal.AssignOp): Bool.True
            (left = NonTerminal.Pat, right = NonTerminal.Pat): Bool.True
            (left = NonTerminal.SimplePat, right = NonTerminal.SimplePat): Bool.True
            (left = NonTerminal.StrPfxBinder, right = NonTerminal.StrPfxBinder): Bool.True
            (left = NonTerminal.RecordFieldPat, right = NonTerminal.RecordFieldPat): Bool.True
            (left = NonTerminal.ImportDecl, right = NonTerminal.ImportDecl): Bool.True
            (left = NonTerminal.TopFunDecl, right = NonTerminal.TopFunDecl): Bool.True
            (left = NonTerminal.TopFunSig, right = NonTerminal.TopFunSig): Bool.True
            (left = NonTerminal.ParentTy, right = NonTerminal.ParentTy): Bool.True
            (left = NonTerminal.Context, right = NonTerminal.Context): Bool.True
            (left = NonTerminal.ParamList, right = NonTerminal.ParamList): Bool.True
            (left = NonTerminal.Param, right = NonTerminal.Param): Bool.True
            (left = NonTerminal.TraitDecl, right = NonTerminal.TraitDecl): Bool.True
            (left = NonTerminal.TraitDeclRhs, right = NonTerminal.TraitDeclRhs): Bool.True
            (left = NonTerminal.FunSig, right = NonTerminal.FunSig): Bool.True
            (left = NonTerminal.ImplDecl, right = NonTerminal.ImplDecl): Bool.True
            (left = NonTerminal.ImplDeclRhs, right = NonTerminal.ImplDeclRhs): Bool.True
            (left = NonTerminal.FunDecl, right = NonTerminal.FunDecl): Bool.True
            (left = NonTerminal.FunDeclRhs, right = NonTerminal.FunDeclRhs): Bool.True
            _: Bool.False

module(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = topDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = topDecl(tokens, cursor)
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
            cursor
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Module, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

topDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
    let altResult = try(||:
        let nonTerminalResult = traitDecl(tokens, cursor)
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
        let nonTerminalResult = implDecl(tokens, cursor)
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
        let nonTerminalResult = topFunDecl(tokens, cursor)
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
                ParseError.UnexpectedToken(cursor = cursor)))

type_(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

recordType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = recordTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        let nonTerminalResult = recordTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        let nonTerminalResult = recordTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
            let nonTerminalResult = recordTypeCont(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

recordTypeStart(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeStart, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParenRow, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeStart, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

recordTypeCont(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordTypeCont, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

variantType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = variantTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        let nonTerminalResult = variantTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        let nonTerminalResult = variantTypeStart(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
            let nonTerminalResult = variantTypeCont(tokens, cursor)
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
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

variantTypeStart(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantTypeStart, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracketRow, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantTypeStart, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

variantTypeCont(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.VariantTypeCont, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

fnType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperFn, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

namedType(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

recordTypeFields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

recordTypeField(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

variantAlt(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = recordTypeFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

fnArgTys(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

typeDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Type, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = typeDeclRhs(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Type, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
            let nonTerminalResult = typeParams(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

typeParams(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

typeDeclRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
                ParseError.UnexpectedToken(cursor = cursor)))

conDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = namedFields(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dedent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

namedFields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
                ParseError.UnexpectedToken(cursor = cursor)))

namedField(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

unnamedFields(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

expr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Expr, nodes), newCursor = newCursor)
    let altResult = try(||:
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Expr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

inlineExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
                ParseError.UnexpectedToken(cursor = cursor)))

blockExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Match, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.If, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Elif, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                let nonTerminalResult = inlineExpr(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                let nonTerminalResult = stmt(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                nodes.push(nonTerminalResult.tree)
                loop:
                    let nodesLen0 = nodes.len()
                    let symResult = try(||:
                        let nonTerminalResult = stmt(tokens, cursor)
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
            let nonTerminalResult = stmt(tokens, cursor)
            cursor = nonTerminalResult.newCursor
            nodes.push(nonTerminalResult.tree)
            loop:
                let nodesLen0 = nodes.len()
                let symResult = try(||:
                    let nonTerminalResult = stmt(tokens, cursor)
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.BlockExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Do, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.PipePipe, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Pipe, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

inlineExprCont(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

prefixExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = exprSuffix(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.PrefixExpr, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

exprSuffix(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = field(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ExprSuffix, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = args(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ExprSuffix, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

field(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Field, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

args(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = arg(tokens, cursor)
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
                        throw(ParseError.UnexpectedToken(cursor = cursor))
                    let nonTerminalResult = arg(tokens, cursor)
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

arg(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Eq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = expr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Arg, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = expr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Arg, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

simpleExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
            let nonTerminalResult = sequence(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                        cursor += 1
                    else:
                        throw(ParseError.UnexpectedToken(cursor = cursor))
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
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        let nonTerminalResult = sequence(tokens, cursor)
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
        if tokens.get(cursor) is Token(kind = TokenKind.Return, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.PipePipe, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Pipe, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimpleExpr, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Int, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

sequence(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Sequence, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = seqElem(tokens, cursor)
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                let nonTerminalResult = seqElem(tokens, cursor)
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Sequence, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

seqElem(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Eq, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SeqElem, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

upperIdPath(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

tyArgs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

parenExpr(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Eq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = expr(tokens, cursor)
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
        let nonTerminalResult = expr(tokens, cursor)
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
                ParseError.UnexpectedToken(cursor = cursor)))

exprPrefix(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Tilde, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.Not, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

binOp(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Plus, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.ExclamationEq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.And, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.Or, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.Pipe, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.Amp, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.RAngle, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.DoubleRAngle, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.RAngleEq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.LAngle, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.DoubleLAngle, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.LAngleEq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

matchAlt(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = pat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = altGuard(tokens, cursor)
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
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
    let altResult = try(||:
        let nonTerminalResult = pat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = altGuard(tokens, cursor)
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
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.MatchAlt, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

altGuard(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.If, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = expr(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.AltGuard, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

matchRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.MatchRhs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

fnArgs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Comma, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                let nodesLen0 = nodes.len()
                let symResult = try(||:
                    if cursor == tokens.len():
                        throw(ParseError.UnexpectedEof)
                    if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                        cursor += 1
                    else:
                        throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

returnTy(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

stmt(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Break, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Label, ..):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Stmt, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Continue, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Label, ..):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Stmt, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Let, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = pat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Eq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = letRhs(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Stmt, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = loopLabel(tokens, cursor)
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
        if tokens.get(cursor) is Token(kind = TokenKind.For, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = pat(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.In, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Stmt, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = loopLabel(tokens, cursor)
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
        if tokens.get(cursor) is Token(kind = TokenKind.While, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Stmt, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = loopLabel(tokens, cursor)
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
        if tokens.get(cursor) is Token(kind = TokenKind.Loop, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Stmt, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = stmtExprCont(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Stmt, nodes), newCursor = newCursor)
    let altResult = try(||:
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Stmt, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

loopLabel(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Label, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.LoopLabel, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

letRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.LetRhs, nodes), newCursor = newCursor)
    let altResult = try(||:
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.LetRhs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

stmtExprCont(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.StmtExprCont, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = assignOp(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.StmtExprCont, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = assignOp(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.StmtExprCont, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

assignOp(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Eq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.AssignOp, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.PlusEq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.AssignOp, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.MinusEq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.AssignOp, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.StarEq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.AssignOp, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.CaretEq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.AssignOp, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

pat(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

simplePat(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
            let nonTerminalResult = recordFieldPat(tokens, cursor)
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
                        throw(ParseError.UnexpectedToken(cursor = cursor))
                    let nonTerminalResult = recordFieldPat(tokens, cursor)
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = recordFieldPat(tokens, cursor)
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
                        throw(ParseError.UnexpectedToken(cursor = cursor))
                    let nonTerminalResult = recordFieldPat(tokens, cursor)
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = recordFieldPat(tokens, cursor)
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
                        throw(ParseError.UnexpectedToken(cursor = cursor))
                    let nonTerminalResult = recordFieldPat(tokens, cursor)
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.DotDot, ..):
                nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = strPfxBinder(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.SimplePat, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Char, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

strPfxBinder(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.StrPfxBinder, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Underscore, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.StrPfxBinder, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

recordFieldPat(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Eq, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordFieldPat, nodes), newCursor = newCursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.RecordFieldPat, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

importDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Import, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                if cursor == tokens.len():
                    throw(ParseError.UnexpectedEof)
                if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
                    nodes.push(ParseTree.Terminal(tokens.get(cursor)))
                    cursor += 1
                else:
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                ParseError.UnexpectedToken(cursor = cursor)))

topFunDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Prim, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = topFunSig(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TopFunDecl, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = topFunSig(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TopFunDecl, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = topFunSig(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TopFunDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

topFunSig(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = parentTy(tokens, cursor)
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
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = context(tokens, cursor)
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
        let nonTerminalResult = paramList(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TopFunSig, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

parentTy(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Dot, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ParentTy, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

context(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Context, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

paramList(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ParamList, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LParen, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = param(tokens, cursor)
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
                let nonTerminalResult = param(tokens, cursor)
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ParamList, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

param(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            if cursor == tokens.len():
                throw(ParseError.UnexpectedEof)
            if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
                cursor += 1
            else:
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.Param, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

traitDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Trait, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = typeParams(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.RBracket, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = traitDeclRhs(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TraitDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

traitDeclRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TraitDeclRhs, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = funDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = funDecl(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.TraitDeclRhs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

funSig(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LowerId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = context(tokens, cursor)
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
        let nonTerminalResult = paramList(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FunSig, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

implDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Impl, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nodesLen0 = nodes.len()
        let symResult = try(||:
            let nonTerminalResult = context(tokens, cursor)
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
        if tokens.get(cursor) is Token(kind = TokenKind.UpperId, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.LBracket, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
                    throw(ParseError.UnexpectedToken(cursor = cursor))
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
                throw(ParseError.UnexpectedToken(cursor = cursor))
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = implDeclRhs(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ImplDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

implDeclRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ImplDeclRhs, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = funDecl(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = funDecl(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.ImplDeclRhs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

funDecl(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Prim, ..):
            nodes.push(ParseTree.Terminal(tokens.get(cursor)))
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = funSig(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FunDecl, nodes), newCursor = newCursor)
    let altResult = try(||:
        let nonTerminalResult = funSig(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        let nonTerminalResult = funDeclRhs(tokens, cursor)
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FunDecl, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))

funDeclRhs(tokens: Vec[Token], cursor: U32) (tree: ParseTree[Token, NonTerminal], newCursor: U32) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.empty()
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FunDeclRhs, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Indent, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = stmt(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        loop:
            let nodesLen0 = nodes.len()
            let symResult = try(||:
                let nonTerminalResult = stmt(tokens, cursor)
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
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FunDeclRhs, nodes), newCursor = newCursor)
    let altResult = try(||:
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Colon, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
        let nonTerminalResult = inlineExpr(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        nodes.push(nonTerminalResult.tree)
        if cursor == tokens.len():
            throw(ParseError.UnexpectedEof)
        if tokens.get(cursor) is Token(kind = TokenKind.Newline, ..):
            cursor += 1
        else:
            throw(ParseError.UnexpectedToken(cursor = cursor))
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
            return (tree = ParseTree.NonTerminal(kind = NonTerminal.FunDeclRhs, nodes), newCursor = newCursor)
    if cursor == tokens.len():
        throw(ParseError.UnexpectedEof)
    else:
        throw(
            curErr.unwrapOrElse(||:
                ParseError.UnexpectedToken(cursor = cursor)))
