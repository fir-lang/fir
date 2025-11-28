main():
    f()

f():
    g()

g():
    t()
    let f = \(): panic("Hi")
    f()

t():
    ()

# expected exit status: 101
# expected stderr:
# tests/PanicStackTrace.fir:9:18: PANIC: Hi
# 
# FIR STACK:
# tests/PanicStackTrace.fir:9:18: Builtin: Panic
# tests/PanicStackTrace.fir:10:5: Closure at tests/PanicStackTrace.fir:9:13
# tests/PanicStackTrace.fir:5:5: g
# tests/PanicStackTrace.fir:2:5: f
# :1:1: main
