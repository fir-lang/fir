# This tests having the same method on the same type, with the same signature,
# once as an associated function and once as a trait method.
#
# Each of the methods can be called by `<type>.<method>(self, ...args)` syntax.
#
# With `self.method(...args)`, we're currently calling the associated function.
# I'm not sure why that is and I don't remember whether this was intentionally
# done. This test makes sure we don't accidentally change it and the self-hosted
# compiler will behave consistently with the reference implementation.


type MyInt(i: U32)


MyInt.__add(self, other: MyInt) MyInt:
    print("Non-trait method")
    MyInt(i = self.i + other.i)


impl Add[MyInt]:
    __add(self: MyInt, other: MyInt) MyInt:
        print("Trait method")
        MyInt(i = self.i + other.i)


main():
    print(MyInt.__add(MyInt(i = 1), MyInt(i = 2)).i)

    # There are issues with the syntax used in the next line, see issue #232. If
    # this syntax becomes invalid, just remove the next line. The line after
    # this one tests the same thing.
    print(Add[MyInt].__add(MyInt(i = 1), MyInt(i = 2)).i)

    print(Add.__add[MyInt, []](MyInt(i = 1), MyInt(i = 2)).i)

    # This currently picks the non-trait method.
    print(MyInt(i = 1).__add(MyInt(i = 2)).i)


# expected stdout:
# Non-trait method
# 3
# Trait method
# 3
# Trait method
# 3
# Non-trait method
# 3
