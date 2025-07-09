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
        Vec.withCapacity(0)

    let rhs: Option[TypeDeclRhs] = if idx < treeNodes.len():
        Option.Some(typeDeclRhsToAst(treeNodes.get(idx).asNonTerminal(NonTerminal.TypeDeclRhs)))
    else:
        Option.None

    TypeDecl(
        name = newId(typeName),
        typeParams,
        typeParamKinds = Vec.withCapacity(0),
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

    panic("TODO")


namedFieldToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) (name: Id, ty: Type):
    # namedField:
    #     "LowerId" _":" type_ _"NEWLINE"

    let name = newId(treeNodes.get(0).asTerminal().text)
    let ty = typeToAst(treeNodes.get(1).asNonTerminal(NonTerminal.Type_))
    (name = name, ty = ty)


typeToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) Type:
    panic("TODO")


newId(name: Str) Id:
    Id(name)
