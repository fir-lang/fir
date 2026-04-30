# Regression test: a record used as an array element type, where the record is
# part of a recursive type with the enclosing array type. The C backend used to
# emit `Array_Record_...` before any forward declaration of the record type,
# producing `unknown type name` errors from the C compiler.


type MyExpr:
    Lit(U32)
    Rec(Vec[(tag: U32, expr: MyExpr)])


main():
    let v = Vec.empty()
    v.push((tag = u32(1), expr = MyExpr.Lit(42)))
    let e = MyExpr.Rec(v)
    if e is MyExpr.Rec(items):
        let item = items.get(0)
        print("`item.tag`")
        if item.expr is MyExpr.Lit(n):
            print("`n`")


# expected stdout:
# 1
# 42
