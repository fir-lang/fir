optionInt() Option[I32] = Option.Some(123)

main():
    match optionInt():
        Option.None: ()
        Option.Some(i): panic("optionInt returned `i`")

# args: --no-backtrace
# expected stderr:
# tests/Panic.fir:6:25: PANIC: optionInt returned 123
