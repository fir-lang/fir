main():
    f()

f():
    g()

g():
    t()
    let f = fn() {
        panic("Hi")
    }
    f()

t():
    ()

# args: --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/PanicStackTrace.fir:10:9: PANIC: Hi
# 
# FIR STACK:
# :1:1: main
# tests/PanicStackTrace.fir:2:5: f
# tests/PanicStackTrace.fir:5:5: g
# tests/PanicStackTrace.fir:12:5: Closure at tests/PanicStackTrace.fir:9:13
# tests/PanicStackTrace.fir:10:9: Builtin: Panic
