fn test[T: ToStr]() =
    printStr("Hi")

fn optionInt(): Option[I32] = Option.Some(123)

fn main() =
    match optionInt():
        Option.None: ()
        Option.Some(i): panic("optionInt returned `i`")

# args: --no-backtrace
# expected stderr:
# tests/Panic.fir:9:25: PANIC: optionInt returned 123
