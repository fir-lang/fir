main():
    let base = (c = "world")
    let r = (a = "hello", b = 42, ..base)
    print(r.a)
    print(r.b)
    print(r.c)

# expected stdout:
# hello
# 42
# world
