test[Add[t]](x: t) (Fn(t) t / exn) / exn:
    x.__add

main():
    let f = test(u32(123))
    print(f(456))

# expected stdout: 579
