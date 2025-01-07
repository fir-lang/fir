# fn f1(): (I8, I32, Option[Str]) = (123, 456, None)

fn f2(): (x: I32, y: I32, optStr: Option[Str]) = (x = 123, y = 456, optStr = Option.Some("Blah"))

fn main()
    # let (x, y, optStr) = f1()
    # printStr(x.toStr())
    # printStr(y.toStr())
    # printStr(optStr.toStr())

    let (x = a, y = b, optStr = c) = f2()
    printStr(a.toStr())
    printStr(b.toStr())
    match c:
        Option.Some(c): printStr(c)
        Option.None: ()

# expected stdout:
# 123
# 456
# Blah
