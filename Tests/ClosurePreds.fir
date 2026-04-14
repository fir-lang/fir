# Regression test: predicates generated inside nested closures should be
# resolved at the enclosing function boundary, not eagerly at the closure
# boundary. Without bubbling closure preds up, the inner closure's pred
# `MyTrait[UVar(a)]` can't match the assumption `MyTrait[RVar(t)]` because
# `UVar(a)` hasn't been unified with `RVar(t)` yet at that point.

trait MyTrait[t]:
    defaultVal() t


type Foo


impl MyTrait[Foo]:
    defaultVal() Foo:
        Foo


makeItem[MyTrait[t]]() t:
    MyTrait[t].defaultVal()


collect[MyTrait[t]]() Vec[t]:
    let items = Vec.withCapacity(1)
    let result = try(
        \():
            items.push(makeItem())
            items,
    )
    match result:
        Result.Ok(v): return v
        Result.Err(_): Vec.withCapacity(0)


main():
    let v: Vec[Foo] = collect()
    print(v.len())


# expected stdout:
# 1
