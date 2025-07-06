import Grammar
import Lexer
import PegTestLib


main(args: Array[Str]):
    runTopDecl("f(): 1")
    runTopDecl("f(x: U32): 1")
    runTopDecl("f(x: U32) U32: 1")
    runTopDecl("f(x: U32) / Exn: 1")
    runTopDecl("f(x: U32) U32 / Exn: 1")
    runTopDecl("\
f():
    a()
    b()")


runTopDecl(input: Str):
    runTestScanner_(input, topDecl)

# expected stdout:
# f(): 1
# TopDecl(
#     TopFunDecl(
#         TopFunSig(LowerId(1:1:"f"), ParamList),
#         InlineExpr(PrefixExpr(SimpleExpr(Int(1:6:"1")))),
#     ),
# )
# 
# f(x: U32): 1
# TopDecl(
#     TopFunDecl(
#         TopFunSig(
#             LowerId(1:1:"f"),
#             ParamList(
#                 Param(LowerId(1:3:"x"), Type_(NamedType(UpperId(1:6:"U32")))),
#             ),
#         ),
#         InlineExpr(PrefixExpr(SimpleExpr(Int(1:12:"1")))),
#     ),
# )
# 
# f(x: U32) U32: 1
# TopDecl(
#     TopFunDecl(
#         TopFunSig(
#             LowerId(1:1:"f"),
#             ParamList(
#                 Param(LowerId(1:3:"x"), Type_(NamedType(UpperId(1:6:"U32")))),
#             ),
#             ReturnTy(Type_(NamedType(UpperId(1:11:"U32")))),
#         ),
#         InlineExpr(PrefixExpr(SimpleExpr(Int(1:16:"1")))),
#     ),
# )
# 
# f(x: U32) / Exn: 1
# TopDecl(
#     TopFunDecl(
#         TopFunSig(
#             LowerId(1:1:"f"),
#             ParamList(
#                 Param(LowerId(1:3:"x"), Type_(NamedType(UpperId(1:6:"U32")))),
#             ),
#             ReturnTy(Slash(1:11:"/"), Type_(NamedType(UpperId(1:13:"Exn")))),
#         ),
#         InlineExpr(PrefixExpr(SimpleExpr(Int(1:18:"1")))),
#     ),
# )
# 
# f(x: U32) U32 / Exn: 1
# TopDecl(
#     TopFunDecl(
#         TopFunSig(
#             LowerId(1:1:"f"),
#             ParamList(
#                 Param(LowerId(1:3:"x"), Type_(NamedType(UpperId(1:6:"U32")))),
#             ),
#             ReturnTy(
#                 Type_(NamedType(UpperId(1:11:"U32"))),
#                 Slash(1:15:"/"),
#                 Type_(NamedType(UpperId(1:17:"Exn"))),
#             ),
#         ),
#         InlineExpr(PrefixExpr(SimpleExpr(Int(1:22:"1")))),
#     ),
# )
# 
# f():
#     a()
#     b()
# TopDecl(
#     TopFunDecl(
#         TopFunSig(LowerId(1:1:"f"), ParamList),
#         Stmt(
#             InlineExpr(
#                 PrefixExpr(
#                     SimpleExpr(LowerId(2:5:"a")),
#                     Args(LParen(2:6:"("), RParen(2:7:")")),
#                 ),
#             ),
#             StmtExprCont,
#         ),
#         Stmt(
#             InlineExpr(
#                 PrefixExpr(
#                     SimpleExpr(LowerId(3:5:"b")),
#                     Args(LParen(3:6:"("), RParen(3:7:")")),
#                 ),
#             ),
#             StmtExprCont,
#         ),
#     ),
# )
