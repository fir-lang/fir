import Grammar
import Lexer
import Peg.PegTestLib


main(args: Array[Str]):
    runTopDecl("impl Foo[T]")

    runTopDecl("\
impl ToStr[T]:
    toStr(self: T) Str:
        1")

    runTopDecl("\
impl[ToStr[a]] ToStr[Vec[a]]:
    toStr(self: Vec[a]) Str:
        1")


runTopDecl(input: Str):
    runTestScanner_(input, topDecl)

# args: -iPeg=tools/peg -iCompiler=compiler

# expected stdout:
# impl Foo[T]
# TopDecl(
#     ImplDecl(
#         UpperId(1:6:"Foo"),
#         Type_(NamedType(UpperId(1:10:"T"))),
#         ImplDeclRhs,
#     ),
# )
# 
# impl ToStr[T]:
#     toStr(self: T) Str:
#         1
# TopDecl(
#     ImplDecl(
#         UpperId(1:6:"ToStr"),
#         Type_(NamedType(UpperId(1:12:"T"))),
#         ImplDeclRhs(
#             FunDecl(
#                 FunSig(
#                     LowerId(2:5:"toStr"),
#                     ParamList(
#                         Param(
#                             LowerId(2:11:"self"),
#                             Type_(NamedType(UpperId(2:17:"T"))),
#                         ),
#                     ),
#                     ReturnTy(Type_(NamedType(UpperId(2:20:"Str")))),
#                 ),
#                 FunDeclRhs(
#                     Stmt(
#                         InlineExpr(PrefixExpr(SimpleExpr(Int(3:9:"1")))),
#                         StmtExprCont,
#                     ),
#                 ),
#             ),
#         ),
#     ),
# )
# 
# impl[ToStr[a]] ToStr[Vec[a]]:
#     toStr(self: Vec[a]) Str:
#         1
# TopDecl(
#     ImplDecl(
#         Context(
#             Type_(NamedType(UpperId(1:6:"ToStr"), Type_(LowerId(1:12:"a")))),
#         ),
#         UpperId(1:16:"ToStr"),
#         Type_(NamedType(UpperId(1:22:"Vec"), Type_(LowerId(1:26:"a")))),
#         ImplDeclRhs(
#             FunDecl(
#                 FunSig(
#                     LowerId(2:5:"toStr"),
#                     ParamList(
#                         Param(
#                             LowerId(2:11:"self"),
#                             Type_(
#                                 NamedType(
#                                     UpperId(2:17:"Vec"),
#                                     Type_(LowerId(2:21:"a")),
#                                 ),
#                             ),
#                         ),
#                     ),
#                     ReturnTy(Type_(NamedType(UpperId(2:25:"Str")))),
#                 ),
#                 FunDeclRhs(
#                     Stmt(
#                         InlineExpr(PrefixExpr(SimpleExpr(Int(3:9:"1")))),
#                         StmtExprCont,
#                     ),
#                 ),
#             ),
#         ),
#     ),
# )
