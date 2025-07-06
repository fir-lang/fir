import Grammar
import Lexer
import PegTestLib


main(args: Array[Str]):
    runTopDecl("trait RecRow[t]")

    runTest_("foo()", funSig)

    runTopDecl("\
trait Blah[t]:
    foo()")

    runTopDecl("\
trait Blah[t]:
    foo(): 1")

    runTopDecl("\
trait Blah[t]:
    foo():
        f()
        g()")


runTopDecl(input: Str):
    runTestScanner_(input, topDecl)

# expected stdout:
# trait RecRow[t]
# TopDecl(
#     TraitDecl(
#         UpperId(1:7:"RecRow"),
#         TypeParams(LowerId(1:14:"t")),
#         TraitDeclRhs,
#     ),
# )
# 
# foo()
# FunSig(LowerId(1:1:"foo"), ParamList)
# 
# trait Blah[t]:
#     foo()
# TopDecl(
#     TraitDecl(
#         UpperId(1:7:"Blah"),
#         TypeParams(LowerId(1:12:"t")),
#         TraitDeclRhs(FunDecl(FunSig(LowerId(2:5:"foo"), ParamList), FunDeclRhs)),
#     ),
# )
# 
# trait Blah[t]:
#     foo(): 1
# TopDecl(
#     TraitDecl(
#         UpperId(1:7:"Blah"),
#         TypeParams(LowerId(1:12:"t")),
#         TraitDeclRhs(
#             FunDecl(
#                 FunSig(LowerId(2:5:"foo"), ParamList),
#                 FunDeclRhs(InlineExpr(PrefixExpr(SimpleExpr(Int(2:12:"1"))))),
#             ),
#         ),
#     ),
# )
# 
# trait Blah[t]:
#     foo():
#         f()
#         g()
# TopDecl(
#     TraitDecl(
#         UpperId(1:7:"Blah"),
#         TypeParams(LowerId(1:12:"t")),
#         TraitDeclRhs(
#             FunDecl(
#                 FunSig(LowerId(2:5:"foo"), ParamList),
#                 FunDeclRhs(
#                     Stmt(
#                         InlineExpr(
#                             PrefixExpr(
#                                 SimpleExpr(LowerId(3:9:"f")),
#                                 ExprSuffix(
#                                     Args(LParen(3:10:"("), RParen(3:11:")")),
#                                 ),
#                             ),
#                         ),
#                         StmtExprCont,
#                     ),
#                     Stmt(
#                         InlineExpr(
#                             PrefixExpr(
#                                 SimpleExpr(LowerId(4:9:"g")),
#                                 ExprSuffix(
#                                     Args(LParen(4:10:"("), RParen(4:11:")")),
#                                 ),
#                             ),
#                         ),
#                         StmtExprCont,
#                     ),
#                 ),
#             ),
#         ),
#     ),
# )
