main():
    # Skip the program name to allow running the test with multiple backends.
    # We may want to consider not including the name in `getArgs`.
    let args = getArgs()
    print(args.slice(1, args.len()).toStr())

# args after: -- a b c
# expected stdout: [a,b,c]
