trait FromStr[t]:
    fromStr(str: Str) t

impl FromStr[U32]:
    fromStr(str: Str) U32:
        987

impl FromStr[Bool]:
    fromStr(str: Str) Bool:
        match str:
            "True": Bool.True
            "False": Bool.False
            _: panic("WAT")

main():
    print(FromStr.fromStr[U32, []]("asdf"))
    print(FromStr.fromStr[Bool, []]("True"))
    print(FromStr.fromStr[Bool, []]("False"))
    let bool: Bool = FromStr.fromStr("True")
    print(bool)

# expected stdout:
# 987
# Bool.True
# Bool.False
# Bool.True
