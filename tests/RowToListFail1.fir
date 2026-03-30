foo[RowToList[r].List = U32](): ()

main():
    foo[row(msg: Str), []]()

# expected exit status: 101
# expected stderr:
# tests/RowToListFail1.fir:4:5: Unable to unify types
#              ListCons[RecordField[Str], []] and
#              U32
#              (
#                 App("ListCons", [App("RecordField", [Con("Str", Star)], Star), Anonymous { labels: {}, extension: None, record_or_variant: Variant, is_row: false }], Star)
#                 Con("U32", Star)
#              )
