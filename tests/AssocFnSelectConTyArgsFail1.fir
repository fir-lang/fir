main():
    let v = Vec[U32].withCapacity[U8, []](10)

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/AssocFnSelectConTyArgsFail1.fir:2:13: Unable to unify types U32 and U8
