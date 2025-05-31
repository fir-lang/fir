
import Lexer
import PegTestLib
import TypeGrammar

main(args: Array[Str])
    if args.len() > 2:
        print("USAGE: One argument to parse argument as type decl")
        print("       No arguments to run unit tests")
        print("       You passed: `args.len() - 1` arguments.")
        panic("")

    if args.len() == 2:
        let result = runTestIndent(args.get(1), typeDecl)
        if !result:
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
    runTest_("Fn(): Foo", type_)
    runTest_("Fn(): exn Foo", type_)
    runTest_("Fn(self)", type_)
    runTest_("Fn(self, a: U32): [] Foo", type_)
    runTest_("Map[Foo, Bar]", type_)

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

    ()

# expected stdout:
# asdf
# Type_(LowerId(1:1:"asdf"))
# 
# Asdf
# Type_(NamedType(UpperId(1:1:"Asdf")))
# 
# ()
# Type_(RecordType)
# 
# (a)
# Type_(RecordType(RecordTypeFields(RecordTypeField(Type_(LowerId(1:2:"a"))))))
# 
# (a, b)
# Type_(
#     RecordType(
#         RecordTypeFields(
#             RecordTypeField(Type_(LowerId(1:2:"a"))),
#             RecordTypeField(Type_(LowerId(1:5:"b"))),
#         ),
#     ),
# )
# 
# (x: T)
# Type_(
#     RecordType(
#         RecordTypeFields(
#             RecordTypeField(
#                 LowerId(1:2:"x"),
#                 Type_(NamedType(UpperId(1:5:"T"))),
#             ),
#         ),
#     ),
# )
# 
# (x: T1, y: T2)
# Type_(
#     RecordType(
#         RecordTypeFields(
#             RecordTypeField(
#                 LowerId(1:2:"x"),
#                 Type_(NamedType(UpperId(1:5:"T1"))),
#             ),
#             RecordTypeField(
#                 LowerId(1:9:"y"),
#                 Type_(NamedType(UpperId(1:12:"T2"))),
#             ),
#         ),
#     ),
# )
# 
# (x: T1, y: T2,)
# Type_(
#     RecordType(
#         RecordTypeFields(
#             RecordTypeField(
#                 LowerId(1:2:"x"),
#                 Type_(NamedType(UpperId(1:5:"T1"))),
#             ),
#             RecordTypeField(
#                 LowerId(1:9:"y"),
#                 Type_(NamedType(UpperId(1:12:"T2"))),
#             ),
#         ),
#     ),
# )
# 
# (x: T1, y: T2, ..r)
# Type_(
#     RecordType(
#         RecordTypeFields(
#             RecordTypeField(
#                 LowerId(1:2:"x"),
#                 Type_(NamedType(UpperId(1:5:"T1"))),
#             ),
#             RecordTypeField(
#                 LowerId(1:9:"y"),
#                 Type_(NamedType(UpperId(1:12:"T2"))),
#             ),
#             LowerId(1:18:"r"),
#         ),
#     ),
# )
# 
# []
# Type_(VariantType)
# 
# [A]
# Type_(VariantType(VariantAlt(UpperId(1:2:"A"))))
# 
# [A, B]
# Type_(VariantType(VariantAlt(UpperId(1:2:"A")), VariantAlt(UpperId(1:5:"B"))))
# 
# [A, B,]
# Type_(VariantType(VariantAlt(UpperId(1:2:"A")), VariantAlt(UpperId(1:5:"B"))))
# 
# [A, B, ..foo]
# Type_(
#     VariantType(
#         VariantAlt(UpperId(1:2:"A")),
#         VariantAlt(UpperId(1:5:"B")),
#         LowerId(1:10:"foo"),
#     ),
# )
# 
# [A(x: U32), B(y: Str), ..foo]
# Type_(
#     VariantType(
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
#         LowerId(1:26:"foo"),
#     ),
# )
# 
# Fn()
# Type_(FnType)
# 
# Fn(): Foo
# Type_(FnType(ReturnType(Type_(NamedType(UpperId(1:7:"Foo"))))))
# 
# Fn(): exn Foo
# Type_(
#     FnType(
#         ReturnType(
#             Type_(LowerId(1:7:"exn")),
#             Type_(NamedType(UpperId(1:11:"Foo"))),
#         ),
#     ),
# )
# 
# Fn(self)
# Type_(FnType(FnArgs(Param(Self(1:4:"self")))))
# 
# Fn(self, a: U32): [] Foo
# Type_(
#     FnType(
#         FnArgs(
#             Param(Self(1:4:"self")),
#             Param(LowerId(1:10:"a"), Type_(NamedType(UpperId(1:13:"U32")))),
#         ),
#         ReturnType(Type_(VariantType), Type_(NamedType(UpperId(1:22:"Foo")))),
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
#             NamedField(
#                 LowerId(3:9:"alts"),
#                 Type_(
#                     NamedType(
#                         UpperId(3:15:"Vec"),
#                         Type_(NamedType(UpperId(3:19:"VariantAlt"))),
#                     ),
#                 ),
#             ),
#             NamedField(
#                 LowerId(4:9:"extension"),
#                 Type_(
#                     NamedType(
#                         UpperId(4:20:"Option"),
#                         Type_(NamedType(UpperId(4:27:"Id"))),
#                     ),
#                 ),
#             ),
#         ),
#     ),
# )

# expected stderr: compiler/Token.fir:138:9: Unexhaustive pattern match

