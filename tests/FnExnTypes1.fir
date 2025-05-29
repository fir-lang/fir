foo(f: Fn(): exn1 ()): exn2 ()
    f()

main()
    foo(fn() { print("Hi") })
    foo(fn() { throw("Hi") })

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/FnExnTypes1.fir:2:5: Unable to unify types exn1 and exn2
