value type List[head, tail](
    head: head,
    tail: Option[tail],
)


impl[ToStr[head], ToStr[tail]] ToStr[List[head, tail]]:
    toStr(self: List[head, tail]) Str:
        match self.tail:
            Option.None: "`self.head`"
            Option.Some(t): "`self.head`, `t`"


impl[ToDoc[head], ToDoc[tail]] ToDoc[List[head, tail]]:
    toDoc(self: List[head, tail]) Doc:
        match self.tail:
            Option.None: self.head.toDoc() + Doc.whenNotFlat(Doc.char(','))
            Option.Some(t):
                self.head.toDoc() + Doc.char(',') + Doc.break_(1) + t.toDoc()


impl[Eq[head], Eq[tail]] Eq[List[head, tail]]:
    __eq(self: List[head, tail], other: List[head, tail]) Bool:
        self.head == other.head and self.tail == other.tail
