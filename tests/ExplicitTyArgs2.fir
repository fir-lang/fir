type True

type False

trait ToBool[t]:
    toBool() Bool

impl ToBool[True]:
    toBool() Bool: Bool.True

impl ToBool[False]:
    toBool() Bool: Bool.False

foo[ToBool[t]]() / exn:
    if ToBool.toBool[t, exn]():
        print("true")
    else:
        print("false")

main():
    foo[True, []]()
    foo[False, []]()

# expected stdout:
# true
# false
