foo(f: Fn(): exn1 ()) exn1 ():
    f()

main():
    foo(fn() { print("Hi") })
    foo(fn() { throw("Hi") })

# args: --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/FnExnTypes2.fir:6:5: Unable to unify types
#              Str and
#              []
#              (
#                 Con("Str", Star)
#                 Anonymous { labels: {}, extension: None, kind: Variant, is_row: false }
#              )
