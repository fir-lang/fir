foo(f: Fn() () / exn1) () / exn1:
    f()

main():
    foo(\(): print("Hi"))
    foo(\(): throw("Hi"))

# expected exit status: 101
# expected stderr:
# Tests/FnExnTypes2.fir:6:5: Unable to unify types
#              Str and
#              []
#              (
#                 Con("Str", Star)
#                 Variant { labels: {}, extension: None, is_row: false }
#              )
