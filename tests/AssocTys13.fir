# Test associated type used in trait method parameter position.

trait Container[t]:
    type Item

    push(self: t, item: Container[t].Item) t
    peek(self: t) Option[Container[t].Item]

type Stack:
    Cons(I32, Stack)
    Nil

impl Container[Stack]:
    type Item = I32

    push(self: Stack, item: Container[Stack].Item) Stack:
        Stack.Cons(item, self)

    peek(self: Stack) Option[Container[Stack].Item]:
        match self:
            Stack.Cons(x, _): Option.Some(x)
            Stack.Nil: Option.None

main():
    let s = Stack.Nil.push(10).push(20)
    print(s.peek().unwrap())

# expected stdout:
# 20
