foo[r: Row[Rec], RecRowToList[r].List = U32]():
    ()


main():
    foo[row(msg: Str), []]()

# expected exit status: 101
# expected stderr:
# tests/RowToListFail1.fir:6:5: Unable to unify types
#              List[RecordField[Str], []] and
#              U32
#              (
#                 App("List", [App("RecordField", [Con("Str", Star)], Star), Anonymous { labels: {}, extension: None, record_or_variant: Variant, is_row: false }], Star)
#                 Con("U32", Star)
#              )
