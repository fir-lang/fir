import Lexer
import PegTestLib
import TypeGrammar

main()
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

# expected stderr: compiler/Token.fir:138:9: Unexhaustive pattern match
