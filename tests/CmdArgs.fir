main():
    printStr(getArgs().toStr())

# args after: -- a b c
# expected stdout: [tests/CmdArgs.fir,a,b,c]
