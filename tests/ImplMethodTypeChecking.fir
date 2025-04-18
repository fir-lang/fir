# Regression test for issue #90.

trait Iter2[iter, item, errs]:
    next2(self: iter): [..errs] Option[item]

    map2(self: iter, f: Fn(item): [..errs] b): [..errs2] Map2[iter, item, b, errs]
        Map2(iter = self, f = f)

type Map2[iter, a, b, varRowErrs]:
    iter: iter
    f: Fn(a): [..varRowErrs] b

impl[Iter2[iter1, a1, errs1]] Iter2[Map2[iter1, a1, b1, errs1], b1, errs1]:
    next2(self: Map2[iter1, a1, b1, errs1]): [..errs1] Option[b1] = panic("")

# args: --typecheck
