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
# tests/interpreter/PanicStackTrace.fir:9:18: PANIC: Hi
# 
# FIR STACK:
# tests/interpreter/PanicStackTrace.fir:9:18: panic
# tests/interpreter/PanicStackTrace.fir:10:5: Closure at tests/interpreter/PanicStackTrace.fir:9:13
# tests/interpreter/PanicStackTrace.fir:5:5: g
# tests/interpreter/PanicStackTrace.fir:2:5: f
# :1:1: main
