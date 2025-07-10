import Ast
import Grammar
import ParseTree


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
            panic("TODO")

        ParseTree.NonTerminal(kind = NonTerminal.TraitDecl, nodes):
            panic("TODO")

        ParseTree.NonTerminal(kind = NonTerminal.ImplDecl, nodes):
            panic("TODO")

        ParseTree.NonTerminal(kind = NonTerminal.TopFunDecl, nodes):
            panic("TODO")

        other:
            panic("Strange top-decl parse tree:\n`other.toDoc().render(80)`")


# --------------------------------------------------------------------------------------------------
# Type declarations


typeDeclToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) TypeDecl:
    # typeDecl:
    #     _"type" "UpperId" (_"[" typeParams _"]")? _":" _"NEWLINE" _"INDENT" typeDeclRhs _"DEDENT"
    #     _"type" "UpperId" (_"[" typeParams _"]")? _"NEWLINE"
    #     "prim" _"type" "UpperId" (_"[" typeParams _"]")? _"NEWLINE"

    let idx = u32(0)

    # Skip 'prim'.
    if treeNodes.get(0) is ParseTree.Terminal(Token(kind = TokenKind.Prim, ..)):
        idx += 1

    let typeName = treeNodes.get(idx).asTerminal().text
    idx += 1

    let typeParams: Vec[Id] = if treeNodes.get(idx + 1) is ParseTree.NonTerminal(kind = NonTerminal.TypeParams, nodes):
        idx += 1
        let typeParams = Vec[Id].withCapacity(nodes.len())
        for node: ParseTree[Token, NonTerminal] in nodes.iter():
            typeParams.push(newId(node.asTerminal().text))
        typeParams
    else:
        Vec.empty()

    let rhs: Option[TypeDeclRhs] = if idx < treeNodes.len():
        Option.Some(typeDeclRhsToAst(treeNodes.get(idx).asNonTerminal(NonTerminal.TypeDeclRhs)))
    else:
        Option.None

    TypeDecl(
        name = newId(typeName),
        typeParams,
        typeParamKinds = Vec.empty(),
        rhs,
    )


typeDeclRhsToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) TypeDeclRhs:
    # typeDeclRhs:
    #     conDecl+
    #     namedField+

    if treeNodes.get(0) is ParseTree.NonTerminal(kind = NonTerminal.ConDecl, nodes):
        let conDecls = Vec[ConDecl].withCapacity(nodes.len())
        for node: ParseTree[Token, NonTerminal] in nodes.iter():
            conDecls.push(conDeclToAst(node.asNonTerminal(NonTerminal.ConDecl)))
        TypeDeclRhs.Sum(conDecls)
    else:
        let fields = Vec[(name: Id, ty: Type)].withCapacity(treeNodes.len())
        for node: ParseTree[Token, NonTerminal] in treeNodes.iter():
            fields.push(namedFieldToAst(node.asNonTerminal(NonTerminal.NamedField)))
        TypeDeclRhs.Product(ConFields.Named(fields))


conDeclToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) ConDecl:
    # "UpperId" _":" _"NEWLINE" _"INDENT" namedFields _"DEDENT"
    # "UpperId" _"(" unnamedFields? _")" _"NEWLINE"
    # "UpperId" _"NEWLINE"

    let name = newId(treeNodes.get(0).asTerminal().text)

    if treeNodes.len() == 1:
        return ConDecl(name = name, fields = ConFields.Empty)

    let fields = if treeNodes.get(1) is ParseTree.NonTerminal(kind = NonTerminal.NamedFields, nodes):
        ConFields.Named(
            nodes
                .iter()
                .map(|node: ParseTree[Token, NonTerminal]|:
                    namedFieldToAst(node.asNonTerminal(NonTerminal.NamedField)))
                .toVec())
    else:
        ConFields.Unnamed(
            treeNodes
                .get(1)
                .asNonTerminal(NonTerminal.UnnamedFields)
                .iter()
                .map(|node: ParseTree[Token, NonTerminal]|:
                    typeToAst(node.asNonTerminal(NonTerminal.Type_)))
                .toVec())

    ConDecl(name, fields)


namedFieldToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) (name: Id, ty: Type):
    # namedField:
    #     "LowerId" _":" type_ _"NEWLINE"

    let name = newId(treeNodes.get(0).asTerminal().text)
    let ty = typeToAst(treeNodes.get(1).asNonTerminal(NonTerminal.Type_))
    (name = name, ty = ty)


# --------------------------------------------------------------------------------------------------
# Types


typeToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) Type:
    # type_:
    #     namedType
    #     "LowerId"
    #     recordType
    #     variantType
    #     fnType

    match treeNodes.get(0):
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


namedTypeToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) NamedType:
    # namedType:
    #     "UpperId" _"[" type_ (_"," type_)* _","? _"]"
    #     "UpperId"

    let name = newId(treeNodes.get(0).asTerminal().text)

    let args = treeNodes
        .iter()
        .skip(1)
        .map(|node: ParseTree[Token, NonTerminal]|:
            typeToAst(node.asNonTerminal(NonTerminal.Type_)))
        .toVec()

    NamedType(name, args)


recordTypeToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) RecordType:
    # recordType:
    #     recordTypeStart _")"
    #     recordTypeStart ".." "LowerId" _")"
    #     recordTypeStart recordTypeField (_"," recordTypeField)* recordTypeCont? _")"
    #
    # recordTypeStart:
    #     "("
    #     "row("

    let isRow =
        treeNodes.get(0).asNonTerminal(NonTerminal.RecordTypeStart).get(0).asTerminal().kind
            is TokenKind.LParenRow

    if treeNodes.get(1) is ParseTree.Terminal(Token(kind = TokenKind.DotDot, ..)):
        let extension = newId(treeNodes.get(2).asTerminal().text)
        return RecordType(
            fields = Vec.empty(),
            extension = Option.Some(extension),
            isRow,
        )

    let fields = Vec[Named[Type]].withCapacity(treeNodes.len() - 1)
    for node: ParseTree[Token, NonTerminal] in treeNodes.iter().skip(1):
        if node is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes):
            fields.push(recordTypeFieldToAst(nodes))
        else:
            break

    let extension = Option.None
    if treeNodes.last().unwrap() is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeCont, nodes):
        extension = recordTypeContToExtension(nodes)

    RecordType(
        fields,
        extension,
        isRow,
    )


recordTypeFieldToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) Named[Type]:
    # recordTypeField:
    #     "LowerId" _":" type_
    #     type_

    let name = if treeNodes.get(0) is ParseTree.Terminal(token):
        Option.Some(newId(token.text))
    else:
        Option.None

    let tyIdx = if name.isSome():
        1
    else:
        0

    let ty = typeToAst(treeNodes.get(1).asNonTerminal(NonTerminal.Type_))

    Named(
        name,
        node = ty,
    )


recordTypeContToExtension(treeNodes: Vec[ParseTree[Token, NonTerminal]]) Option[Id]:
    # recordTypeCont:
    #     _"," (_".." "LowerId")?

    if treeNodes.len() == 1:
        return Option.None

    Option.Some(newId(treeNodes.get(0).asTerminal().text))


variantTypeToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) VariantType:
    # variantType:
    #     variantTypeStart _"]"
    #     variantTypeStart _".." "LowerId" _"]"
    #     variantTypeStart variantAlt (_"," variantAlt)* variantTypeCont? _"]"
    #
    # variantTypeStart:
    #     "["
    #     "row["

    let isRow =
            treeNodes.get(0).asNonTerminal(NonTerminal.VariantTypeStart).get(0).asTerminal().kind
                is TokenKind.LBracketRow

    if treeNodes.get(1) is ParseTree.Terminal(Token(kind = TokenKind.DotDot, ..)):
        let extension = newId(treeNodes.get(2).asTerminal().text)
        return VariantType(
            alts = Vec.empty(),
            extension = Option.Some(extension),
            isRow,
        )

    let alts = Vec[VariantAlt].withCapacity(treeNodes.len() - 1)
    for node: ParseTree[Token, NonTerminal] in treeNodes.iter().skip(1):
        if node is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes):
            alts.push(variantAltToAst(nodes))
        else:
            break

    let extension = Option.None
    if treeNodes.last().unwrap() is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeCont, nodes):
        extension = recordTypeContToExtension(nodes)

    VariantType(
        alts,
        extension,
        isRow,
    )


variantAltToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) VariantAlt:
    # variantAlt:
    #     "UpperId" _"(" recordTypeFields _")"
    #     "UpperId"
    #
    # recordTypeFields:
    #     recordTypeField (_"," recordTypeField)* _"," _".." "LowerId"
    #     recordTypeField (_"," recordTypeField)* _","?

    let con = newId(treeNodes.get(0).asTerminal().text)

    if treeNodes.len() == 1:
        return VariantAlt(con, fields = Vec.empty())

    let treeNodes = treeNodes.get(1).asNonTerminal(NonTerminal.RecordTypeFields)

    let fields = Vec[Named[Type]].withCapacity(treeNodes.len() - 1)
    for node: ParseTree[Token, NonTerminal] in treeNodes.iter():
        if node is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeField, nodes):
            fields.push(recordTypeFieldToAst(nodes))
        else:
            break

    let extension = Option.None
    if treeNodes.last().unwrap() is ParseTree.NonTerminal(kind = NonTerminal.RecordTypeCont, nodes):
        extension = recordTypeContToExtension(nodes)

    VariantAlt(con, fields)


fnTypeToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) FnType:
    # fnType:
    #     _"Fn" _"(" fnArgTys? _")" returnTy?

    if treeNodes.isEmpty():
        return FnType(args = Vec.empty(), ret = Option.None, exceptions = Option.None)

    let retIdx = 0

    let args = if treeNodes.get(0) is ParseTree.NonTerminal(kind = NonTerminal.FnArgTys, nodes):
        retIdx += 1
        Option.Some(fnArgTysToAst(nodes))
    else:
        Option.None

    panic("TODO")


fnArgTysToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) Vec[Type]:
    # fnArgTys:
    #     type_ (_"," type_)* _","?
    panic("TODO")


returnTyToAst(nodes: Vec[ParseTree[Token, NonTerminal]]) (ret: Type, exn: Type):
    # returnTyToAst:
    #     type_ "/" type_
    #     type_
    #     "/" type_

    panic("TODO")


# --------------------------------------------------------------------------------------------------


newId(name: Str) Id:
    Id(name)
