main
    let s = "asdf"
    let iter = s.chars().peekable()
    for x in iter:
        printStr(iter.peek().toStr())
        printStr(x.toStr())
