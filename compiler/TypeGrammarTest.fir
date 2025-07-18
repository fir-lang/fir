import Grammar
import Lexer
import Peg.PegTestLib

main(args: Array[Str]):
    if args.len() > 2:
        print("USAGE: One argument to parse argument as type decl")
        print("       No arguments to run unit tests")
        print("       You passed: `args.len() - 1` arguments.")
        panic("")

    if args.len() == 2:
        let result = runTestIndent(args.get(1), typeDecl)
        if not result:
            print("FAIL")
        return

    runTest_("asdf", type_)
    runTest_("Asdf", type_)
    runTest_("()", type_)
    runTest_("(a)", type_)
    runTest_("(a, b)", type_)
    runTest_("(x: T)", type_)
    runTest_("(x: T1, y: T2)", type_)
    runTest_("(x: T1, y: T2,)", type_)
    runTest_("(x: T1, y: T2, ..r)", type_)
    runTest_("[]", type_)
    runTest_("[A]", type_)
    runTest_("[A, B]", type_)
    runTest_("[A, B,]", type_)
    runTest_("[A, B, ..foo]", type_)
    runTest_("[A(x: U32), B(y: Str), ..foo]", type_)
    runTest_("Fn()", type_)
    runTest_("Fn() Foo", type_)
    runTest_("Fn() Foo / exn", type_)
    runTest_("Fn(self)", type_)
    runTest_("Fn(self, U32) Foo / []", type_)
    runTest_("Map[Foo, Bar]", type_)
    runTest_("[]", type_)
    runTest_("[Foo, Bar]", type_)
    runTest_("[Foo, Bar,]", type_)
    runTest_("[Foo(x: Str), ..x]", type_)

    runTestIndent("\
type Foo:
    a: U32", typeDecl)

    runTestIndent("\
type Option[t]:
    None
    Some(t)", typeDecl)

    runTestIndent("\
type VecIter[t]:
    _vec: Vec[t]
    _idx: U32", typeDecl)

    runTestIndent("\
type Result[e, t]:
    Err(e)
    Ok(t)", typeDecl)

    runTestIndent("\
type _SpaceReq:
    Exact(U32)
    Infinite", typeDecl)

    runTestIndent("prim type U64", typeDecl)

    runTestIndent("\
type Type:
    Variant:
        alts: Vec[VariantAlt]
        extension: Option[Id]", typeDecl)

    runTestIndent("\
type MapResult[iter, item, b, exnOld, exnNew]:
    iter: iter
    f: Fn(Result[exnOld, Option[item]]) Option[b] / exnNew", typeDecl)

    ()

# args: -iPeg=tools/peg -iCompiler=compiler

# expected stdout:
# asdf
# Type_(LowerId(1:1:"asdf"))
# 
# Asdf
# Type_(NamedType(UpperId(1:1:"Asdf")))
# 
# ()
# Type_(RecordType(RecordTypeStart(LParen(1:1:"("))))
# 
# (a)
# Type_(
#     RecordType(
#         RecordTypeStart(LParen(1:1:"(")),
#         RecordTypeField(Type_(LowerId(1:2:"a"))),
#     ),
# )
# 
# (a, b)
# Type_(
#     RecordType(
#         RecordTypeStart(LParen(1:1:"(")),
#         RecordTypeField(Type_(LowerId(1:2:"a"))),
#         RecordTypeField(Type_(LowerId(1:5:"b"))),
#     ),
# )
# 
# (x: T)
# Type_(
#     RecordType(
#         RecordTypeStart(LParen(1:1:"(")),
#         RecordTypeField(LowerId(1:2:"x"), Type_(NamedType(UpperId(1:5:"T")))),
#     ),
# )
# 
# (x: T1, y: T2)
# Type_(
#     RecordType(
#         RecordTypeStart(LParen(1:1:"(")),
#         RecordTypeField(LowerId(1:2:"x"), Type_(NamedType(UpperId(1:5:"T1")))),
#         RecordTypeField(LowerId(1:9:"y"), Type_(NamedType(UpperId(1:12:"T2")))),
#     ),
# )
# 
# (x: T1, y: T2,)
# Type_(
#     RecordType(
#         RecordTypeStart(LParen(1:1:"(")),
#         RecordTypeField(LowerId(1:2:"x"), Type_(NamedType(UpperId(1:5:"T1")))),
#         RecordTypeField(LowerId(1:9:"y"), Type_(NamedType(UpperId(1:12:"T2")))),
#         RecordTypeCont,
#     ),
# )
# 
# (x: T1, y: T2, ..r)
# Type_(
#     RecordType(
#         RecordTypeStart(LParen(1:1:"(")),
#         RecordTypeField(LowerId(1:2:"x"), Type_(NamedType(UpperId(1:5:"T1")))),
#         RecordTypeField(LowerId(1:9:"y"), Type_(NamedType(UpperId(1:12:"T2")))),
#         RecordTypeCont(LowerId(1:18:"r")),
#     ),
# )
# 
# []
# Type_(VariantType(VariantTypeStart(LBracket(1:1:"["))))
# 
# [A]
# Type_(
#     VariantType(
#         VariantTypeStart(LBracket(1:1:"[")),
#         VariantAlt(UpperId(1:2:"A")),
#     ),
# )
# 
# [A, B]
# Type_(
#     VariantType(
#         VariantTypeStart(LBracket(1:1:"[")),
#         VariantAlt(UpperId(1:2:"A")),
#         VariantAlt(UpperId(1:5:"B")),
#     ),
# )
# 
# [A, B,]
# Type_(
#     VariantType(
#         VariantTypeStart(LBracket(1:1:"[")),
#         VariantAlt(UpperId(1:2:"A")),
#         VariantAlt(UpperId(1:5:"B")),
#         VariantTypeCont,
#     ),
# )
# 
# [A, B, ..foo]
# Type_(
#     VariantType(
#         VariantTypeStart(LBracket(1:1:"[")),
#         VariantAlt(UpperId(1:2:"A")),
#         VariantAlt(UpperId(1:5:"B")),
#         VariantTypeCont(LowerId(1:10:"foo")),
#     ),
# )
# 
# [A(x: U32), B(y: Str), ..foo]
# Type_(
#     VariantType(
#         VariantTypeStart(LBracket(1:1:"[")),
#         VariantAlt(
#             UpperId(1:2:"A"),
#             RecordTypeFields(
#                 RecordTypeField(
#                     LowerId(1:4:"x"),
#                     Type_(NamedType(UpperId(1:7:"U32"))),
#                 ),
#             ),
#         ),
#         VariantAlt(
#             UpperId(1:13:"B"),
#             RecordTypeFields(
#                 RecordTypeField(
#                     LowerId(1:15:"y"),
#                     Type_(NamedType(UpperId(1:18:"Str"))),
#                 ),
#             ),
#         ),
#         VariantTypeCont(LowerId(1:26:"foo")),
#     ),
# )
# 
# Fn()
# Type_(FnType)
# 
# Fn() Foo
# Type_(FnType(ReturnTy(Type_(NamedType(UpperId(1:6:"Foo"))))))
# 
# Fn() Foo / exn
# Type_(
#     FnType(
#         ReturnTy(
#             Type_(NamedType(UpperId(1:6:"Foo"))),
#             Slash(1:10:"/"),
#             Type_(LowerId(1:12:"exn")),
#         ),
#     ),
# )
# 
# Fn(self)
# Type_(FnType(FnArgTys(Type_(LowerId(1:4:"self")))))
# 
# Fn(self, U32) Foo / []
# Type_(
#     FnType(
#         FnArgTys(
#             Type_(LowerId(1:4:"self")),
#             Type_(NamedType(UpperId(1:10:"U32"))),
#         ),
#         ReturnTy(
#             Type_(NamedType(UpperId(1:15:"Foo"))),
#             Slash(1:19:"/"),
#             Type_(VariantType(VariantTypeStart(LBracket(1:21:"[")))),
#         ),
#     ),
# )
# 
# Map[Foo, Bar]
# Type_(
#     NamedType(
#         UpperId(1:1:"Map"),
#         Type_(NamedType(UpperId(1:5:"Foo"))),
#         Type_(NamedType(UpperId(1:10:"Bar"))),
#     ),
# )
# 
# []
# Type_(VariantType(VariantTypeStart(LBracket(1:1:"["))))
# 
# [Foo, Bar]
# Type_(
#     VariantType(
#         VariantTypeStart(LBracket(1:1:"[")),
#         VariantAlt(UpperId(1:2:"Foo")),
#         VariantAlt(UpperId(1:7:"Bar")),
#     ),
# )
# 
# [Foo, Bar,]
# Type_(
#     VariantType(
#         VariantTypeStart(LBracket(1:1:"[")),
#         VariantAlt(UpperId(1:2:"Foo")),
#         VariantAlt(UpperId(1:7:"Bar")),
#         VariantTypeCont,
#     ),
# )
# 
# [Foo(x: Str), ..x]
# Type_(
#     VariantType(
#         VariantTypeStart(LBracket(1:1:"[")),
#         VariantAlt(
#             UpperId(1:2:"Foo"),
#             RecordTypeFields(
#                 RecordTypeField(
#                     LowerId(1:6:"x"),
#                     Type_(NamedType(UpperId(1:9:"Str"))),
#                 ),
#             ),
#         ),
#         VariantTypeCont(LowerId(1:17:"x")),
#     ),
# )
# 
# type Foo:
#     a: U32
# TypeDecl(
#     UpperId(1:6:"Foo"),
#     TypeDeclRhs(
#         NamedField(LowerId(2:5:"a"), Type_(NamedType(UpperId(2:8:"U32")))),
#     ),
# )
# 
# type Option[t]:
#     None
#     Some(t)
# TypeDecl(
#     UpperId(1:6:"Option"),
#     TypeParams(LowerId(1:13:"t")),
#     TypeDeclRhs(
#         ConDecl(UpperId(2:5:"None")),
#         ConDecl(UpperId(3:5:"Some"), UnnamedFields(Type_(LowerId(3:10:"t")))),
#     ),
# )
# 
# type VecIter[t]:
#     _vec: Vec[t]
#     _idx: U32
# TypeDecl(
#     UpperId(1:6:"VecIter"),
#     TypeParams(LowerId(1:14:"t")),
#     TypeDeclRhs(
#         NamedField(
#             LowerId(2:5:"_vec"),
#             Type_(NamedType(UpperId(2:11:"Vec"), Type_(LowerId(2:15:"t")))),
#         ),
#         NamedField(LowerId(3:5:"_idx"), Type_(NamedType(UpperId(3:11:"U32")))),
#     ),
# )
# 
# type Result[e, t]:
#     Err(e)
#     Ok(t)
# TypeDecl(
#     UpperId(1:6:"Result"),
#     TypeParams(LowerId(1:13:"e"), LowerId(1:16:"t")),
#     TypeDeclRhs(
#         ConDecl(UpperId(2:5:"Err"), UnnamedFields(Type_(LowerId(2:9:"e")))),
#         ConDecl(UpperId(3:5:"Ok"), UnnamedFields(Type_(LowerId(3:8:"t")))),
#     ),
# )
# 
# type _SpaceReq:
#     Exact(U32)
#     Infinite
# TypeDecl(
#     UpperId(1:6:"_SpaceReq"),
#     TypeDeclRhs(
#         ConDecl(
#             UpperId(2:5:"Exact"),
#             UnnamedFields(Type_(NamedType(UpperId(2:11:"U32")))),
#         ),
#         ConDecl(UpperId(3:5:"Infinite")),
#     ),
# )
# 
# prim type U64
# TypeDecl(Prim(1:1:"prim"), UpperId(1:11:"U64"))
# 
# type Type:
#     Variant:
#         alts: Vec[VariantAlt]
#         extension: Option[Id]
# TypeDecl(
#     UpperId(1:6:"Type"),
#     TypeDeclRhs(
#         ConDecl(
#             UpperId(2:5:"Variant"),
#             NamedFields(
#                 NamedField(
#                     LowerId(3:9:"alts"),
#                     Type_(
#                         NamedType(
#                             UpperId(3:15:"Vec"),
#                             Type_(NamedType(UpperId(3:19:"VariantAlt"))),
#                         ),
#                     ),
#                 ),
#                 NamedField(
#                     LowerId(4:9:"extension"),
#                     Type_(
#                         NamedType(
#                             UpperId(4:20:"Option"),
#                             Type_(NamedType(UpperId(4:27:"Id"))),
#                         ),
#                     ),
#                 ),
#             ),
#         ),
#     ),
# )
# 
# type MapResult[iter, item, b, exnOld, exnNew]:
#     iter: iter
#     f: Fn(Result[exnOld, Option[item]]) Option[b] / exnNew
# TypeDecl(
#     UpperId(1:6:"MapResult"),
#     TypeParams(
#         LowerId(1:16:"iter"),
#         LowerId(1:22:"item"),
#         LowerId(1:28:"b"),
#         LowerId(1:31:"exnOld"),
#         LowerId(1:39:"exnNew"),
#     ),
#     TypeDeclRhs(
#         NamedField(LowerId(2:5:"iter"), Type_(LowerId(2:11:"iter"))),
#         NamedField(
#             LowerId(3:5:"f"),
#             Type_(
#                 FnType(
#                     FnArgTys(
#                         Type_(
#                             NamedType(
#                                 UpperId(3:11:"Result"),
#                                 Type_(LowerId(3:18:"exnOld")),
#                                 Type_(
#                                     NamedType(
#                                         UpperId(3:26:"Option"),
#                                         Type_(LowerId(3:33:"item")),
#                                     ),
#                                 ),
#                             ),
#                         ),
#                     ),
#                     ReturnTy(
#                         Type_(
#                             NamedType(
#                                 UpperId(3:41:"Option"),
#                                 Type_(LowerId(3:48:"b")),
#                             ),
#                         ),
#                         Slash(3:51:"/"),
#                         Type_(LowerId(3:53:"exnNew")),
#                     ),
#                 ),
#             ),
#         ),
#     ),
# )
