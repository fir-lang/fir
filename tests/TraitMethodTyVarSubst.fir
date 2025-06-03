trait Test[a, b]:
    test(self: a) b

type AB[a, b]:
    a: a
    b: b

impl Test[AB[b, a], a]:
    test(self: AB[b, a]) a:
        self.b
        
main():
    printStr(AB(a = 1, b = "Hi").test())

# expected stdout: Hi
