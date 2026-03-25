test():
    ()

main():
    test[row[]]()

# expected exit status: 101
# expected stderr:
# tests/VariantRowConfusion.fir:5:5: Unable to unify types row[] and [] (kind mismatch, row(variant) ~ *)
