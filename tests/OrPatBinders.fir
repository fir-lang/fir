type Tree:
    Leaf(U32)
    Branch(Tree, Tree, U32)

main():
    let t1 = Tree.Leaf(123u32)
    match t1:
        Tree.Leaf(x) | Tree.Branch(_, _, x) print(x)

    let t2 = Tree.Branch(Tree.Leaf(1u32), Tree.Leaf(2u32), 123u32)
    match t2:
        Tree.Leaf(x) | Tree.Branch(_, _, x) print(x)

    let t3 = Tree.Branch(Tree.Leaf(123u32), Tree.Branch(Tree.Leaf(1u32), Tree.Leaf(2u32), 3u32), 4u32)
    match t3:
        Tree.Leaf(x) | Tree.Branch(Tree.Leaf(x) | Tree.Branch(Tree.Leaf(_), Tree.Leaf(x), _), _, _) print(x)

    let t4 = Tree.Leaf(123u32)
    match t4:
        Tree.Leaf(x) | Tree.Branch(Tree.Leaf(x) | Tree.Branch(Tree.Leaf(_), Tree.Leaf(x), _), _, _) print(x)

    let t5 = Tree.Branch(Tree.Branch(Tree.Leaf(1u32), Tree.Leaf(123u32), 2u32), Tree.Leaf(3u32), 4u32)
    match t5:
        Tree.Leaf(x) | Tree.Branch(Tree.Leaf(x) | Tree.Branch(Tree.Leaf(_), Tree.Leaf(x), _), _, _) print(x)

# expected stdout:
# 123
# 123
# 123
# 123
# 123

# expected stderr:
# tests/OrPatBinders.fir:15:5: Unexhaustive pattern match
# tests/OrPatBinders.fir:19:5: Unexhaustive pattern match
# tests/OrPatBinders.fir:23:5: Unexhaustive pattern match
