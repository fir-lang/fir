test[Add[t]](x: t) (Fn(t) t / exn) / exn:
    x.__add

main():
    let f = test(123u32)
    print(f(456))

# expected stdout: 579
