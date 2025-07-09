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
    runBlockExprScan("\
match foo:
    A: 1
    B: 2")

    # If
    runBlockExprScan("\
if foo:
    a()")
    runBlockExprScan("\
if foo:
    1
else:
    2")
    runBlockExprScan("\
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
    runBlockExprScan("\
||:
    f()
    g()")

    ()


runInlineExpr(input: Str):
    runTest_(input, inlineExpr)


runInlineExprScan(input: Str):
    runTestScanner_(input, inlineExpr)


runBlockExprScan(input: Str):
    runTestScanner_(input, blockExpr)

# expected stdout:
# hi
# InlineExpr(PrefixExpr(SimpleExpr(LowerId(1:1:"hi"))))
# 
# Foo
# InlineExpr(PrefixExpr(SimpleExpr(UpperIdPath(UpperId(1:1:"Foo")))))
# 
# Foo.Bar
# InlineExpr(
#     PrefixExpr(SimpleExpr(UpperIdPath(UpperId(1:1:"Foo"), UpperId(1:5:"Bar")))),
# )
# 
# ~Foo
# InlineExpr(PrefixExpr(SimpleExpr(UpperIdPath(TildeUpperId(1:1:"~Foo")))))
# 
# ~Foo.Bar
# InlineExpr(
#     PrefixExpr(
#         SimpleExpr(UpperIdPath(TildeUpperId(1:1:"~Foo"), UpperId(1:6:"Bar"))),
#     ),
# )
# 
# foo.bar
# InlineExpr(
#     PrefixExpr(
#         SimpleExpr(LowerId(1:1:"foo")),
#         ExprSuffix(Field(LowerId(1:5:"bar"))),
#     ),
# )
# 
# Foo.bar
# InlineExpr(
#     PrefixExpr(
#         SimpleExpr(UpperIdPath(UpperId(1:1:"Foo"))),
#         ExprSuffix(Field(LowerId(1:5:"bar"))),
#     ),
# )
# 
# foo(bar)
# InlineExpr(
#     PrefixExpr(
#         SimpleExpr(LowerId(1:1:"foo")),
#         ExprSuffix(
#             Args(
#                 Arg(
#                     Expr(InlineExpr(PrefixExpr(SimpleExpr(LowerId(1:5:"bar"))))),
#                 ),
#             ),
#         ),
#     ),
# )
# 
# 123
# InlineExpr(PrefixExpr(SimpleExpr(Int(1:1:"123"))))
# 
# "hi"
# InlineExpr(PrefixExpr(SimpleExpr(Str(1:1:"\"hi\""))))
# 
# 'a'
# InlineExpr(PrefixExpr(SimpleExpr(Char(1:1:"'a'"))))
# 
# self
# InlineExpr(PrefixExpr(SimpleExpr(LowerId(1:1:"self"))))
# 
# 1 + 2
# InlineExpr(
#     PrefixExpr(SimpleExpr(Int(1:1:"1"))),
#     InlineExprCont(BinOp(Plus(1:3:"+")), PrefixExpr(SimpleExpr(Int(1:5:"2")))),
# )
# 
# 1 + 2 - 3
# InlineExpr(
#     PrefixExpr(SimpleExpr(Int(1:1:"1"))),
#     InlineExprCont(BinOp(Plus(1:3:"+")), PrefixExpr(SimpleExpr(Int(1:5:"2")))),
#     InlineExprCont(BinOp(Minus(1:7:"-")), PrefixExpr(SimpleExpr(Int(1:9:"3")))),
# )
# 
# -1
# InlineExpr(PrefixExpr(ExprPrefix(Minus(1:1:"-")), SimpleExpr(Int(1:2:"1"))))
# 
# (x = 123, y = "hi")
# InlineExpr(
#     PrefixExpr(
#         SimpleExpr(
#             LParen(1:1:"("),
#             ParenExpr(
#                 LowerId(1:2:"x"),
#                 Eq(1:4:"="),
#                 Expr(InlineExpr(PrefixExpr(SimpleExpr(Int(1:6:"123"))))),
#             ),
#             ParenExpr(
#                 LowerId(1:11:"y"),
#                 Eq(1:13:"="),
#                 Expr(InlineExpr(PrefixExpr(SimpleExpr(Str(1:15:"\"hi\""))))),
#             ),
#             RParen(1:19:")"),
#         ),
#     ),
# )
# 
# return
# InlineExpr(PrefixExpr(SimpleExpr(Return(1:1:"return"))))
# 
# return 123
# InlineExpr(
#     PrefixExpr(
#         SimpleExpr(
#             Return(1:1:"return"),
#             InlineExpr(PrefixExpr(SimpleExpr(Int(1:8:"123")))),
#         ),
#     ),
# )
# 
# match foo:
#     A: 1
#     B: 2
# BlockExpr(
#     Match(1:1:"match"),
#     InlineExpr(PrefixExpr(SimpleExpr(LowerId(1:7:"foo")))),
#     MatchAlt(
#         Pat(SimplePat(UpperIdPath(UpperId(2:5:"A")))),
#         Stmt(InlineExpr(PrefixExpr(SimpleExpr(Int(2:8:"1")))), StmtExprCont),
#     ),
#     MatchAlt(
#         Pat(SimplePat(UpperIdPath(UpperId(3:5:"B")))),
#         Stmt(InlineExpr(PrefixExpr(SimpleExpr(Int(3:8:"2")))), StmtExprCont),
#     ),
# )
# 
# if foo:
#     a()
# BlockExpr(
#     If(1:1:"if"),
#     InlineExpr(PrefixExpr(SimpleExpr(LowerId(1:4:"foo")))),
#     Stmt(
#         InlineExpr(PrefixExpr(SimpleExpr(LowerId(2:5:"a")), ExprSuffix(Args))),
#         StmtExprCont,
#     ),
# )
# 
# if foo:
#     1
# else:
#     2
# BlockExpr(
#     If(1:1:"if"),
#     InlineExpr(PrefixExpr(SimpleExpr(LowerId(1:4:"foo")))),
#     Stmt(InlineExpr(PrefixExpr(SimpleExpr(Int(2:5:"1")))), StmtExprCont),
#     Else(3:1:"else"),
#     Stmt(InlineExpr(PrefixExpr(SimpleExpr(Int(4:5:"2")))), StmtExprCont),
# )
# 
# if foo:
#     1
# elif bar:
#     2
# else:
#     3
# BlockExpr(
#     If(1:1:"if"),
#     InlineExpr(PrefixExpr(SimpleExpr(LowerId(1:4:"foo")))),
#     Stmt(InlineExpr(PrefixExpr(SimpleExpr(Int(2:5:"1")))), StmtExprCont),
#     Elif(3:1:"elif"),
#     InlineExpr(PrefixExpr(SimpleExpr(LowerId(3:6:"bar")))),
#     Stmt(InlineExpr(PrefixExpr(SimpleExpr(Int(4:5:"2")))), StmtExprCont),
#     Else(5:1:"else"),
#     Stmt(InlineExpr(PrefixExpr(SimpleExpr(Int(6:5:"3")))), StmtExprCont),
# )
# 
# x is C
# InlineExpr(
#     PrefixExpr(SimpleExpr(LowerId(1:1:"x"))),
#     InlineExprCont(Is(1:3:"is"), Pat(SimplePat(UpperIdPath(UpperId(1:6:"C"))))),
# )
# 
# x is C == Bool.True
# InlineExpr(
#     PrefixExpr(SimpleExpr(LowerId(1:1:"x"))),
#     InlineExprCont(Is(1:3:"is"), Pat(SimplePat(UpperIdPath(UpperId(1:6:"C"))))),
#     InlineExprCont(
#         BinOp(EqEq(1:8:"==")),
#         PrefixExpr(
#             SimpleExpr(UpperIdPath(UpperId(1:11:"Bool"), UpperId(1:16:"True"))),
#         ),
#     ),
# )
# 
# ||: a
# InlineExpr(
#     PrefixExpr(
#         SimpleExpr(
#             PipePipe(1:1:"||"),
#             Colon(1:3:":"),
#             InlineExpr(PrefixExpr(SimpleExpr(LowerId(1:5:"a")))),
#         ),
#     ),
# )
# 
# ||:
#     f()
#     g()
# BlockExpr(
#     PipePipe(1:1:"||"),
#     Colon(1:3:":"),
#     Stmt(
#         InlineExpr(PrefixExpr(SimpleExpr(LowerId(2:5:"f")), ExprSuffix(Args))),
#         StmtExprCont,
#     ),
#     Stmt(
#         InlineExpr(PrefixExpr(SimpleExpr(LowerId(3:5:"g")), ExprSuffix(Args))),
#         StmtExprCont,
#     ),
# )
