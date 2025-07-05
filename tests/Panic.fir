optionInt() Option[I32]: Option.Some(123)

main():
    match optionInt():
        Option.None: ()
        Option.Some(i): panic("optionInt returned `i`")

# args: --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/Panic.fir:6:25: PANIC: optionInt returned 123
# 
# FIR STACK:
# :1:1: main
# tests/Panic.fir:6:25: Builtin: Panic
