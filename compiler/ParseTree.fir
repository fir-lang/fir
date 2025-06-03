type ParseTree[t, nt]:
    Terminal(t)

    NonTerminal:
        kind: nt
        nodes: Vec[ParseTree[t, nt]]

type ParseError[t]:
    UnexpectedEof
    UnexpectedToken(t)

impl[ToStr[t], ToStr[nt]] ToStr[ParseTree[t, nt]]:
    toStr(self: ParseTree[t, nt]) Str:
        self.toDoc().print(80)

impl[ToStr[t]] ToStr[ParseError[t]]:
    toStr(self: ParseError[t]) Str:
        match self:
            ParseError.UnexpectedEof: "unexpected end of input"
            ParseError.UnexpectedToken(t): "unexpected token `t`"

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
            panic("ParseTree.getNonTerminal: tree is a terminal")
        ParseTree.NonTerminal(kind, nodes):
            if kind != kind_:
                panic("ParseTree.getNonTerminal: expected `kind_`, found `kind`")
            nodes
