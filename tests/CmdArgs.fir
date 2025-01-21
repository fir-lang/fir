main(args: Array[Str])
    printStr(args.toStr())

# TODO: https://github.com/jfecher/golden-tests/issues/10
# goldentests currently pass extra arguments before the program path, which is
# not how interpreters work usually. We should fix this and test passing
# arguments here.

# expected stdout: [tests/CmdArgs.fir]
