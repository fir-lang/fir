type UserState(
    a: U32,
    b: U32,
    c: U32,
)


impl ToStr[UserState]:
    toStr(self: UserState) Str:
        "UserState(a = `self.a`, b = `self.b`, c = `self.c`)"
