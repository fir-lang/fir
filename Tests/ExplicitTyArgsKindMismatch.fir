# inferred type: `[exn: Row[Var]] Fn() U32 / [Str, ..exn]`
foo() U32 / [Str, ..exn]:
    throw(~"hi")


main():
    # Kind mismatch: passes `*` type, but function expects `Row[Var]`.
    let x = try(\(): foo[[]]())

# expected exit status: 101
# expected stderr:
# Tests/ExplicitTyArgsKindMismatch.fir:8:22: Unable to pass type argument [] as Row[Var] (kind mismatch)
