import Compiler.Assert
import Compiler.Ast
import Compiler.Grammar
import Peg.ParseTree


main():
    print("hi")


moduleToAst(module: ParseTree[Token, NonTerminal]) Vec[TopDecl]:
    let decls = Vec[TopDecl].withCapacity(10)

    for topDecl in module.asNonTerminal(NonTerminal.Module).iter():
        topDeclToAst(topDecl)

    decls


topDeclToAst(topDecl: ParseTree[Token, NonTerminal]) TopDecl:
    match topDecl:
        ParseTree.NonTerminal(kind = NonTerminal.TypeDecl, nodes):
            TopDecl.Type(typeDeclToAst(nodes))

        ParseTree.NonTerminal(kind = NonTerminal.ImportDecl, nodes):
            TopDecl.Import(importDeclToAst(nodes))

        ParseTree.NonTerminal(kind = NonTerminal.TraitDecl, nodes):
            TopDecl.Trait(traitDeclToAst(nodes))

        ParseTree.NonTerminal(kind = NonTerminal.ImplDecl, nodes):
            TopDecl.Impl(implDeclToAst(nodes))

        ParseTree.NonTerminal(kind = NonTerminal.TopFunDecl, nodes):
            TopDecl.Fun(funDeclToAst(nodes))

        other:
            panic("Strange top-decl parse tree:\n`other.toDoc().render(80)`")


# --------------------------------------------------------------------------------------------------
# Type declarations


typeDeclToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) TypeDecl:
    # typeDecl:
    #     _"type" "UpperId" (_"[" typeParams _"]")? _":" _"NEWLINE" _"INDENT" typeDeclRhs _"DEDENT"
    #     _"type" "UpperId" (_"[" typeParams _"]")? _"NEWLINE"
    #     "prim" _"type" "UpperId" (_"[" typeParams _"]")? _"NEWLINE"

    let idx = u32(0)

    # Skip 'prim'.
    if nodes.get(0) is ParseTree.Terminal(Token(kind = TokenKind.Prim, ..)):
        idx += 1

    let typeName = nodes.get(idx).asTerminal().text
    idx += 1

    let typeParams: Vec[Id] = if nodes.get(idx + 1) is ParseTree.NonTerminal(kind = NonTerminal.TypeParams, nodes):
        idx += 1
        typeParamsToAst(nodes)
    else:
        Vec.empty()

    let rhs: Option[TypeDeclRhs] = if idx < nodes.len():
        Option.Some(typeDeclRhsToAst(nodes.get(idx).asNonTerminal(NonTerminal.TypeDeclRhs)))
    else:
        Option.None

    TypeDecl(
        name = newId(typeName),
        typeParams,
        typeParamKinds = Vec.empty(),
        rhs,
    )


typeParamsToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) Vec[Id]:
    let typeParams = Vec[Id].withCapacity(nodes.len())
    for node: ParseTree[Token, NonTerminal] in nodes.iter():
        typeParams.push(newId(node.asTerminal().text))
    typeParams


typeDeclRhsToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) TypeDeclRhs:
    # typeDeclRhs:
    #     conDecl+
    #     namedField+

    if nodes.get(0) is ParseTree.NonTerminal(kind = NonTerminal.ConDecl, nodes):
        let conDecls = Vec[ConDecl].withCapacity(nodes.len())
        for node: ParseTree[Token, NonTerminal] in nodes.iter():
            conDecls.push(conDeclToAst(node.asNonTerminal(NonTerminal.ConDecl)))
        TypeDeclRhs.Sum(conDecls)
    else:
        let fields = Vec[(name: Id, ty: Type)].withCapacity(nodes.len())
        for node: ParseTree[Token, NonTerminal] in nodes.iter():
            fields.push(namedFieldToAst(node.asNonTerminal(NonTerminal.NamedField)))
        TypeDeclRhs.Product(ConFields.Named(fields))


conDeclToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) ConDecl:
    # "UpperId" _":" _"NEWLINE" _"INDENT" namedFields _"DEDENT"
    # "UpperId" _"(" unnamedFields? _")" _"NEWLINE"
    # "UpperId" _"NEWLINE"

    let name = newId(nodes.get(0).asTerminal().text)

    if nodes.len() == 1:
        return ConDecl(name = name, fields = ConFields.Empty)

    let fields = if nodes.get(1) is ParseTree.NonTerminal(kind = NonTerminal.NamedFields, nodes):
        ConFields.Named(
            nodes
                .iter()
                .map(|node: ParseTree[Token, NonTerminal]|:
                    namedFieldToAst(node.asNonTerminal(NonTerminal.NamedField)))
                .toVec())
    else:
        ConFields.Unnamed(
            nodes
                .get(1)
                .asNonTerminal(NonTerminal.UnnamedFields)
                .iter()
                .map(|node: ParseTree[Token, NonTerminal]|:
                    typeToAst(node.asNonTerminal(NonTerminal.Type_)))
                .toVec())

    ConDecl(name, fields)


namedFieldToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) (name: Id, ty: Type):
    # namedField:
    #     "LowerId" _":" type_ _"NEWLINE"

    let name = newId(nodes.get(0).asTerminal().text)
    let ty = typeToAst(nodes.get(1).asNonTerminal(NonTerminal.Type_))
    (name = name, ty = ty)


# --------------------------------------------------------------------------------------------------
# Types


typeToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) Type:
    # type_:
    #     namedType
    #     "LowerId"
    #     recordType
    #     variantType
    #     fnType

    match nodes.get(0):
        ParseTree.NonTerminal(kind = NonTerminal.NamedType, nodes):
            Type.Named(namedTypeToAst(nodes))

        ParseTree.Terminal(Token(kind = TokenKind.LowerId, text, ..)):
            Type.Var(newId(text))

        ParseTree.NonTerminal(kind = NonTerminal.RecordType, nodes):
            Type.Record(recordTypeToAst(nodes))

        ParseTree.NonTerminal(kind = NonTerminal.VariantType, nodes):
            Type.Variant(variantTypeToAst(nodes))

        ParseTree.NonTerminal(kind = NonTerminal.FnType, nodes):
            Type.Fn_(fnTypeToAst(nodes))

        other:
            panic("Strange type parse tree:\n`other.toDoc().render(80)`")


namedTypeToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) NamedType:
    # namedType:
    #     "UpperId" _"[" type_ (_"," type_)* _","? _"]"
    #     "UpperId"

    let name = newId(nodes.get(0).asTerminal().text)

    let args = nodes
        .iter()
        .skip(1)
        .map(|node: ParseTree[Token, NonTerminal]|:
            typeToAst(node.asNonTerminal(NonTerminal.Type_)))
        .toVec()

    NamedType(name, args)


recordTypeToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) RecordType:
    # recordType:
    #     recordTypeStart _")"
    #     recordTypeStart ".." "LowerId" _")"
    #     recordTypeStart recordTypeField (_"," recordTypeField)* recordTypeCont? _")"
    #
    # recordTypeStart:
    #     "("
    #     "row("

    let isRow =
        nodes.get(0).asNonTerminal(NonTerminal.RecordTypeStart).get(0).asTerminal().kind
            is TokenKind.LParenRow

    if nodes.get(1) is ParseTree.Terminal(Token(kind = TokenKind.DotDot, ..)):
        let extension = newId(nodes.get(2).asTerminal().text)
        return RecordType(
            fields = Vec.empty(),
            extension = Option.Some(extension),
            isRow,
        )

    let fields = Vec[Named[Type]].withCapacity(nodes.len() - 1)
    for node: ParseTree[Token, NonTerminal] in nodes.iter().skip(1):
        if node is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes):
            fields.push(recordTypeFieldToAst(nodes))
        else:
            break

    let extension = Option.None
    if nodes.last().unwrap() is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeCont, nodes):
        extension = recordTypeContToExtension(nodes)

    RecordType(
        fields,
        extension,
        isRow,
    )


recordTypeFieldToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) Named[Type]:
    # recordTypeField:
    #     "LowerId" _":" type_
    #     type_

    let name = if nodes.get(0) is ParseTree.Terminal(token):
        Option.Some(newId(token.text))
    else:
        Option.None

    let tyIdx = if name.isSome():
        1
    else:
        0

    let ty = typeToAst(nodes.get(1).asNonTerminal(NonTerminal.Type_))

    Named(
        name,
        node = ty,
    )


recordTypeContToExtension(nodes: Vec[ParseTree[Token, NonTerminal]]) Option[Id]:
    # recordTypeCont:
    #     _"," (_".." "LowerId")?

    if nodes.len() == 1:
        return Option.None

    Option.Some(newId(nodes.get(0).asTerminal().text))


variantTypeToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) VariantType:
    # variantType:
    #     variantTypeStart _"]"
    #     variantTypeStart _".." "LowerId" _"]"
    #     variantTypeStart variantAlt (_"," variantAlt)* variantTypeCont? _"]"
    #
    # variantTypeStart:
    #     "["
    #     "row["

    let isRow =
            nodes.get(0).asNonTerminal(NonTerminal.VariantTypeStart).get(0).asTerminal().kind
                is TokenKind.LBracketRow

    if nodes.get(1) is ParseTree.Terminal(Token(kind = TokenKind.DotDot, ..)):
        let extension = newId(nodes.get(2).asTerminal().text)
        return VariantType(
            alts = Vec.empty(),
            extension = Option.Some(extension),
            isRow,
        )

    let alts = Vec[VariantAlt].withCapacity(nodes.len() - 1)
    for node: ParseTree[Token, NonTerminal] in nodes.iter().skip(1):
        if node is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes):
            alts.push(variantAltToAst(nodes))
        else:
            break

    let extension = Option.None
    if nodes.last().unwrap() is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeCont, nodes):
        extension = recordTypeContToExtension(nodes)

    VariantType(
        alts,
        extension,
        isRow,
    )


variantAltToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) VariantAlt:
    # variantAlt:
    #     "UpperId" _"(" recordTypeFields _")"
    #     "UpperId"
    #
    # recordTypeFields:
    #     recordTypeField (_"," recordTypeField)* _"," _".." "LowerId"
    #     recordTypeField (_"," recordTypeField)* _","?

    let con = newId(nodes.get(0).asTerminal().text)

    if nodes.len() == 1:
        return VariantAlt(con, fields = Vec.empty())

    let nodes = nodes.get(1).asNonTerminal(NonTerminal.RecordTypeFields)

    let fields = Vec[Named[Type]].withCapacity(nodes.len() - 1)
    for node: ParseTree[Token, NonTerminal] in nodes.iter():
        if node is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes):
            fields.push(recordTypeFieldToAst(nodes))
        else:
            break

    let extension = Option.None
    if nodes.last().unwrap() is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeCont, nodes):
        extension = recordTypeContToExtension(nodes)

    VariantAlt(con, fields)


fnTypeToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) FnType:
    # fnType:
    #     _"Fn" _"(" fnArgTys? _")" returnTy?

    if nodes.isEmpty():
        return FnType(args = Vec.empty(), ret = Option.None, exceptions = Option.None)

    let retIdx = 0

    let args = if nodes.get(0) is ParseTree.NonTerminal(kind = NonTerminal.FnArgTys, nodes):
        retIdx += 1
        fnArgTysToAst(nodes)
    else:
        Vec.empty()

    let ret = if nodes.last().unwrap() is ParseTree.NonTerminal(kind = NonTerminal.ReturnTy, nodes):
        returnTyToAst(nodes)
    else:
        (ret = Option.None, exn = Option.None)

    FnType(
        args,
        ret = ret.ret,
        exceptions = ret.exn,
    )


fnArgTysToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) Vec[Type]:
    # fnArgTys:
    #     type_ (_"," type_)* _","?

    nodes
        .iter()
        .map(|node: ParseTree[Token, NonTerminal]|:
            typeToAst(node.asNonTerminal(NonTerminal.Type_)))
        .toVec()


returnTyToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) (ret: Option[Type], exn: Option[Type]):
    # returnTyToAst:
    #     type_ "/" type_
    #     type_
    #     "/" type_

    if nodes.len() == 1:
        (
            ret = Option.Some(typeToAst(nodes.get(0).asNonTerminal(NonTerminal.Type_))),
            exn = Option.None
        )
    elif nodes.len() == 2:
        (
            ret = Option.None,
            exn = Option.Some(typeToAst(nodes.get(0).asNonTerminal(NonTerminal.Type_)))
        )
    else:
        assertEq(nodes.len(), 3)
        (
            ret = Option.Some(typeToAst(nodes.get(0).asNonTerminal(NonTerminal.Type_))),
            exn = Option.Some(typeToAst(nodes.get(2).asNonTerminal(NonTerminal.Type_))),
        )


# --------------------------------------------------------------------------------------------------
# Import declarations


importDeclToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) ImportDecl:
    # importDecl:
    #     "import" "UpperId" (_"." "UpperId")* _"NEWLINE"

    ImportDecl(
        path = nodes
            .iter()
            .map(|node: ParseTree[Token, NonTerminal]|: node.asTerminal().text)
            .toVec())


# --------------------------------------------------------------------------------------------------
# Trait declarations


traitDeclToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) TraitDecl:
    # traitDecl:
    #     _"trait" "UpperId" _"[" typeParams _"]" traitDeclRhs?

    let name = newId(nodes.get(0).asTerminal().text)

    let typeParams = typeParamsToAst(nodes.get(1).asNonTerminal(NonTerminal.TypeParams))

    panic("TODO")


# --------------------------------------------------------------------------------------------------
# Impl declarations


implDeclToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) ImplDecl:
    panic("TODO")


# --------------------------------------------------------------------------------------------------
# Function declarations


funDeclToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) FunDecl:
    panic("TODO")


topFunSigToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) FunSig:
    let idx: U32 = 0
    let parentTy: Option[Id] = Option.None
    if nodes.get(0) is ParseTree.NonTerminal(kind = NonTerminal.ParentTy, nodes):
        parentTy = Option.Some(newId(nodes.get(0).asTerminal().text))
        idx += 1

    let sig = funSigToAst

    panic("TODO")


funSigToAst(nodes: Vec[ParseTree[Token, NonTerminal]], startIdx: U32) FunSig:
    let idx = startIdx
    let name = newId(nodes.get(idx).asTerminal().text)

    let preds = if nodes.get(1) is ParseTree.NonTerminal(kind = NonTerminal.Context, nodes):
        idx += 1
        contextToAst(nodes)
    else:
        Vec.empty()

    let context = Context(typeParams = Vec.empty(), preds)

    let params = paramListToAst(nodes.get(idx).asNonTerminal(NonTerminal.ParamList))
    idx += 1

    let ret = if idx < nodes.len():
        returnTyToAst(nodes.get(idx).asNonTerminal(NonTerminal.ReturnTy))
    else:
        (ret = Option.None, exn = Option.None)

    panic("TODO")


paramListToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) Vec[(name: Str, ty: Type)]:
    panic("TODO")


# --------------------------------------------------------------------------------------------------


contextToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) Vec[Type]:
    nodes
        .iter()
        .map(|node: ParseTree[Token, NonTerminal]|: typeToAst(node.asNonTerminal(NonTerminal.Type_)))
        .toVec()


newId(name: Str) Id:
    Id(name)
