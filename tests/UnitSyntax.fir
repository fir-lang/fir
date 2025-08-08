type MyUnit

type MyUnitGeneric[t]

type MyProduct(x: U32)

type MyProductGeneric[t](x: t)

main():
    let unit1 = MyUnit
    f(unit1)

    let unit2 = MyUnitGeneric[U32]
    g(unit2)

    let unit3: MyUnitGeneric[U32] = MyUnitGeneric
    g(unit2)

    let product1 = MyProduct(x = 123)
    let product2 = MyProductGeneric[U32](x = 123)

    print(product1.x)
    print(product2.x)

f(x: MyUnit): ()
g(x: MyUnitGeneric[t]): ()

# expected stdout:
# 123
# 123
