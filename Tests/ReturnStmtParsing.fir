f():
    return match foo:
        Option.Some(_): Bool.True
        Option.None: Bool.False


g():
    return if x > u32(0):
        Bool.True
    else:
        Bool.False


h():
    return do:
        print("a")
        y + 2


# args: --parse
