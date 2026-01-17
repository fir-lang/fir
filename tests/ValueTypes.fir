# This test will be updated to use the types when we implement value types in
# the backends.


value type MyBool:
    True
    False


value type MyChar(_codePoint: U32)


value type T1[t](t)


value type T2[t](t)


impl[ToStr[t]] ToStr[T1[t]]:
    toStr(self: T1[t]) Str:
        match self:
            T1(x): "T1(`x`)"


impl[ToStr[t]] ToStr[T2[t]]:
    toStr(self: T2[t]) Str:
        match self:
            T2(x): "T2(`x`)"


main():
    let x: T1[T2[T1[()]]] = T1(T2(T1(())))
    print(x)
