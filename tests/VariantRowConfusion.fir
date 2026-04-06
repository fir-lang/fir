# inferred type: `[?exn: *] Fn() () / ?exn`
test():
    ()

main():
    # Kind mismatch: passes `Row[Var]`, but function expects `*`.
    test[row[]]()

# expected exit status: 101
# expected stderr:
# tests/VariantRowConfusion.fir:7:5: Unable to pass type argument row[] as * (kind mismatch)
