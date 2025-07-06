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

    # TODO: Match, If, Fn, Is

    ()


runInlineExpr(input: Str):
    runTest_(input, inlineExpr)
