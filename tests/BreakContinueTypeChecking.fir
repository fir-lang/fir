main
    loop:
        let x: U32 = match f():
            Option.None:
                print("break")
                break
            Option.Some(i):
                i
        print(x)

    let i: U32 = 0
    loop:
        i += 1
        if i == 2:
            break
        let x: U32 = match f():
            Option.None:
                print("continue")
                continue
            Option.Some(i):
                i
        print(x)

f: Option[U32] = Option.None

# expected stdout:
# break
# continue
