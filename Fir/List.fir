value type ListCons[head, tail](
    head: head,
    tail: Option[tail],
)


impl[ToStr[head], ToStr[tail]] ToStr[ListCons[head, tail]]:
    toStr(self: ListCons[head, tail]) Str:
        match self.tail:
            Option.None: "`self.head`"
            Option.Some(t): "`self.head`, `t`"


impl[ToDoc[head], ToDoc[tail]] ToDoc[ListCons[head, tail]]:
    toDoc(self: ListCons[head, tail]) Doc:
        match self.tail:
            Option.None: self.head.toDoc() + Doc.whenNotFlat(Doc.char(','))
            Option.Some(t):
                self.head.toDoc() + Doc.char(',') + Doc.break_(1) + t.toDoc()


impl[Eq[head], Eq[tail]] Eq[ListCons[head, tail]]:
    __eq(self: ListCons[head, tail], other: ListCons[head, tail]) Bool:
        self.head == other.head and self.tail == other.tail
