type ParseTree[t, nt]:
    Terminal(t)

    NonTerminal:
        kind: nt
        nodes: Vec[ParseTree[t, nt]]

type ParseError[t]:
    UnexpectedEof
    UnexpectedToken:
        token: t
        cursor: U32

ParseError.takeAdvanced(err1: ParseError[t], err2: ParseError[t]) ParseError[t]:
    if err1 is ParseError.UnexpectedToken(cursor = c1, ..)
            and err2 is ParseError.UnexpectedToken(cursor = c2, ..):
        if c1 > c2:
            return err1
        else:
            return err2

    ParseError.UnexpectedEof

impl[ToStr[t], ToStr[nt]] ToStr[ParseTree[t, nt]]:
    toStr(self: ParseTree[t, nt]) Str:
        self.toDoc().render(80)

impl[ToStr[t]] ToStr[ParseError[t]]:
    toStr(self: ParseError[t]) Str:
        match self:
            ParseError.UnexpectedEof: "unexpected end of input"
            ParseError.UnexpectedToken(token, cursor): "unexpected token `token` at cursor `cursor`"

ParseTree.toDoc[ToStr[t], ToStr[nt]](self: ParseTree[t, nt]) Doc:
    match self:
        ParseTree.Terminal(t):
            Doc.str(t.toStr())

        ParseTree.NonTerminal(kind, nodes):
            if nodes.len() == 0:
                return Doc.str(kind.toStr())

            let doc = Doc.str(kind.toStr()) + Doc.char('(') + Doc.break_(0)
            let nodeIdx: U32 = 0
            for node: ParseTree[t, nt] in nodes.iter():
                if nodeIdx != 0:
                    doc += Doc.char(',') + Doc.break_(1)
                doc += node.toDoc()
                nodeIdx += 1

            # Add a trailing comma when splitting the node list into lines.
            doc += Doc.whenNotFlat(Doc.char(','))

            (doc.nest(4) + Doc.break_(0) + Doc.char(')')).group()

ParseTree.asTerminal(self: ParseTree[t, nt]) t:
    match self:
        ParseTree.Terminal(t): t
        ParseTree.NonTerminal(..): panic("ParseTree.asTerminal: tree is a non-terminal")

ParseTree.asNonTerminal[Eq[nt], ToStr[nt]](self: ParseTree[t, nt], kind_: nt) Vec[ParseTree[t, nt]]:
    match self:
        ParseTree.Terminal(_):
            panic("ParseTree.asNonTerminal: tree is a terminal")
        ParseTree.NonTerminal(kind, nodes):
            if kind != kind_:
                panic("ParseTree.asNonTerminal: expected `kind_`, found `kind`")
            nodes
