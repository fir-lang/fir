removeX(r: (x: t, ..rest)) (..rest):
    match r:
        (x = _, ..rest): rest

removeY(r: (y: t, ..rest)) (..rest):
    match r:
        (y = _, ..rest): rest

main():
    print(removeY(removeX((x = u32(1), y = u32(2), msg = "hi"))).msg)
