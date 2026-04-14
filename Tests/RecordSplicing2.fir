makeRecord() (a: U32, b: Str):
    (a = 1, b = "hello")

main():
    let r = (..makeRecord())
    print(r.a)
    print(r.b)

# expected stdout:
# 1
# hello
