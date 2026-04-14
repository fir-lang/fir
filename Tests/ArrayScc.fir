type T:
    T1
    T2(Array[T])


impl ToStr[T]:
    toStr(self: T) Str:
        match self:
            T.T1: "T.T1"
            T.T2(array): "T.T2(`array`)"

main():
    print(T.T1)
    print(T.T2(Array.fromIter([T.T1], 1)))

# expected stdout:
# T.T1
# T.T2([T.T1])
