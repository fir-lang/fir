import Grammar
import Lexer
import PegTestLib


main(args: Array[Str]):
    # Var
    runInlineExpr("hi")

    # ConstructorSelect: product
    runInlineExpr("Foo")

    # ConstructorSelect: sum
    runInlineExpr("Foo.Bar")
    runInlineExpr("~Foo")
    runInlineExpr("~Foo.Bar")

    # FieldSelect
    runInlineExpr("foo.bar")

    # AssocFnSelect
    runInlineExpr("Foo.bar")

    # Call
    runInlineExpr("foo(bar)")

    # Int
    runInlineExpr("123")

    # Str
    runInlineExpr("\"hi\"")

    # Char
    runInlineExpr("'a'")

    # Self
    runInlineExpr("self")

    # BinOp
    runInlineExpr("1 + 2")
    runInlineExpr("1 + 2 - 3")

    # UnOp
    runInlineExpr("-1")

    # Record
    runInlineExpr("(x = 123, y = \"hi\")")

    # Return
    runInlineExpr("return")
    runInlineExpr("return 123")

    # Match
    runInlineExprScan("\
match foo:
    A: 1
    B: 2")

    # If
    runInlineExprScan("\
if foo:
    a()")
    runInlineExprScan("\
if foo:
    1
else:
    2")
    runInlineExprScan("\
if foo:
    1
elif bar:
    2
else:
    3")

    # Is
    runInlineExpr("x is C")
    runInlineExpr("x is C == Bool.True")

    # Function exprs
    runInlineExpr("||: a")
    runInlineExprScan("\
||:
    f()
    g()")

    ()


runInlineExpr(input: Str):
    runTest_(input, inlineExpr)


runInlineExprScan(input: Str):
    runTestScanner_(input, inlineExpr)
