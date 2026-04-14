type Alias[t] = Vec[t]

main():
    let v: Alias[U32, Str] = Vec.withCapacity(10)

# expected exit status: 101
# expected stderr:
# Tests/TypeSynonymParamsFailArity.fir:4:12: Incorrect number of type arguments to Alias, expected 1, found 2
