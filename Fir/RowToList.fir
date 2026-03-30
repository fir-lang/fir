# This trait will only be implemented by the compiler, for record types, as
# needed.
trait RowToList[recRow]:
    type List

    rowToList(rec: (..recRow)) Option[List]


type RecordField[t](
    label: Str,
    value_: t,
)


impl[ToStr[t]] ToStr[RecordField[t]]:
    toStr(self: RecordField[t]) Str:
        "`self.label` = `self.value_`"


impl[ToDoc[t]] ToDoc[RecordField[t]]:
    toDoc(self: RecordField[t]) Doc:
        Doc.str(self.label)
            + Doc.blank(1)
            + Doc.char('=')
            + Doc.blank(1)
            + self.value_.toDoc()


impl[Eq[t]] Eq[RecordField[t]]:
    __eq(self: RecordField[t], other: RecordField[t]) Bool:
        self.label == other.label and self.value_ == other.value_


impl[ToStr[RowToList[r].List]] ToStr[(..r)]:
    toStr(self: (..r)) Str:
        match RowToList[r].rowToList(self):
            Option.None: "()"
            Option.Some(list): "(`list`)"


impl[ToDoc[RowToList[r].List]] ToDoc[(..r)]:
    toDoc(self: (..r)) Doc:
        match RowToList[r].rowToList(self):
            Option.None: Doc.str("()")
            Option.Some(list):
                Doc.grouped(
                    Doc.nested(4, Doc.char('(') + Doc.break_(0) + list.toDoc())
                        + Doc.break_(0)
                        + Doc.char(')'),
                )


impl[Eq[RowToList[r].List]] Eq[(..r)]:
    __eq(self: (..r), other: (..r)) Bool:
        RowToList[r].rowToList(self) == RowToList[r].rowToList(other)

    # Explicitly implement `__neq`, the default method calls a method on `self` and we don't support
    # method calls on records yet.
    __neq(self: (..r), other: (..r)) Bool:
        not (RowToList[r].rowToList(self) == RowToList[r].rowToList(other))
