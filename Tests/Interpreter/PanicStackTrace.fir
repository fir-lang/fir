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
# Tests/Interpreter/PanicStackTrace.fir:9:18: PANIC: Hi
# 
# FIR STACK:
# Tests/Interpreter/PanicStackTrace.fir:9:18: panic
# Tests/Interpreter/PanicStackTrace.fir:10:5: Closure at Tests/Interpreter/PanicStackTrace.fir:9:13
# Tests/Interpreter/PanicStackTrace.fir:5:5: g
# Tests/Interpreter/PanicStackTrace.fir:2:5: f
# :1:1: main
