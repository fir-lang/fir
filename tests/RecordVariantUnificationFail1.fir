main():
    let x: [] = ()

# expected exit status: 101
# expected stderr:
# tests/RecordVariantUnificationFail1.fir:2:17: Unable to unify types
#              () and
#              []
#              (
#                 Anonymous { labels: {}, extension: None, record_or_variant: Record, is_row: false }
#                 Anonymous { labels: {}, extension: None, record_or_variant: Variant, is_row: false }
#              )
