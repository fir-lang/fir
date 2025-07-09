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
            typeDeclToAst(nodes)
            # TODO: We need a Loc
            panic("TODO")

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
        panic("TODO")


conDeclToAst(treeNodes: Vec[ParseTree[Token, NonTerminal]]) ConDecl:
    panic("TODO")


newId(name: Str) Id:
    Id(name)
