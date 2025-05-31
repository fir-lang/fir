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
    runTest_("Fn()", type_)
    runTest_("Fn(): Foo", type_)
    runTest_("Fn(): exn Foo", type_)
    runTest_("Fn(self)", type_)
    runTest_("Fn(self, a: U32): [] Foo", type_)

# Asdf
# Type_(NamedType(UpperId(1:1:"Asdf")))
#
# ()
# Type_(LParen(1:1:"("), RParen(1:2:")"))
#
# (a)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(RecordTypeField(Type_(LowerId(1:2:"a")))),
#     RParen(1:3:")"),
# )
#
# (a, b)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(
#         RecordTypeField(Type_(LowerId(1:2:"a"))),
#         Comma(1:3:","),
#         RecordTypeField(Type_(LowerId(1:5:"b"))),
#     ),
#     RParen(1:6:")"),
# )
#
# (x: T)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(
#         RecordTypeField(
#             LowerId(1:2:"x"),
#             Colon(1:3:":"),
#             Type_(NamedType(UpperId(1:5:"T"))),
#         ),
#     ),
#     RParen(1:6:")"),
# )
#
# (x: T1, y: T2)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(
#         RecordTypeField(
#             LowerId(1:2:"x"),
#             Colon(1:3:":"),
#             Type_(NamedType(UpperId(1:5:"T1"))),
#         ),
#         Comma(1:7:","),
#         RecordTypeField(
#             LowerId(1:9:"y"),
#             Colon(1:10:":"),
#             Type_(NamedType(UpperId(1:12:"T2"))),
#         ),
#     ),
#     RParen(1:14:")"),
# )
#
# (x: T1, y: T2,)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(
#         RecordTypeField(
#             LowerId(1:2:"x"),
#             Colon(1:3:":"),
#             Type_(NamedType(UpperId(1:5:"T1"))),
#         ),
#         Comma(1:7:","),
#         RecordTypeField(
#             LowerId(1:9:"y"),
#             Colon(1:10:":"),
#             Type_(NamedType(UpperId(1:12:"T2"))),
#         ),
#         Comma(1:14:","),
#     ),
#     RParen(1:15:")"),
# )
#
# (x: T1, y: T2, ..r)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(
#         RecordTypeField(
#             LowerId(1:2:"x"),
#             Colon(1:3:":"),
#             Type_(NamedType(UpperId(1:5:"T1"))),
#         ),
#         Comma(1:7:","),
#         RecordTypeField(
#             LowerId(1:9:"y"),
#             Colon(1:10:":"),
#             Type_(NamedType(UpperId(1:12:"T2"))),
#         ),
#         Comma(1:14:","),
#         DotDot(1:16:".."),
#         LowerId(1:18:"r"),
#     ),
#     RParen(1:19:")"),
# )
#
# []
# Type_(LBracket(1:1:"["), RBracket(1:2:"]"))
#
# [A]
# Type_(LBracket(1:1:"["), VariantAlt(UpperId(1:2:"A")), RBracket(1:3:"]"))
#
# [A, B]
# Type_(
#     LBracket(1:1:"["),
#     VariantAlt(UpperId(1:2:"A")),
#     Comma(1:3:","),
#     VariantAlt(UpperId(1:5:"B")),
#     RBracket(1:6:"]"),
# )
#
# [A, B,]
# Type_(
#     LBracket(1:1:"["),
#     VariantAlt(UpperId(1:2:"A")),
#     Comma(1:3:","),
#     VariantAlt(UpperId(1:5:"B")),
#     Comma(1:6:","),
#     RBracket(1:7:"]"),
# )
#
# [A, B, ..foo]
# Type_(
#     LBracket(1:1:"["),
#     VariantAlt(UpperId(1:2:"A")),
#     Comma(1:3:","),
#     VariantAlt(UpperId(1:5:"B")),
#     Comma(1:6:","),
#     DotDot(1:8:".."),
#     LowerId(1:10:"foo"),
#     RBracket(1:13:"]"),
# )

# expected stdout:
# asdf
# Type_(LowerId(1:1:"asdf"))
# 
# Asdf
# Type_(NamedType(UpperId(1:1:"Asdf")))
# 
# ()
# Type_(LParen(1:1:"("), RParen(1:2:")"))
# 
# (a)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(RecordTypeField(Type_(LowerId(1:2:"a")))),
#     RParen(1:3:")"),
# )
# 
# (a, b)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(
#         RecordTypeField(Type_(LowerId(1:2:"a"))),
#         Comma(1:3:","),
#         RecordTypeField(Type_(LowerId(1:5:"b"))),
#     ),
#     RParen(1:6:")"),
# )
# 
# (x: T)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(
#         RecordTypeField(
#             LowerId(1:2:"x"),
#             Colon(1:3:":"),
#             Type_(NamedType(UpperId(1:5:"T"))),
#         ),
#     ),
#     RParen(1:6:")"),
# )
# 
# (x: T1, y: T2)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(
#         RecordTypeField(
#             LowerId(1:2:"x"),
#             Colon(1:3:":"),
#             Type_(NamedType(UpperId(1:5:"T1"))),
#         ),
#         Comma(1:7:","),
#         RecordTypeField(
#             LowerId(1:9:"y"),
#             Colon(1:10:":"),
#             Type_(NamedType(UpperId(1:12:"T2"))),
#         ),
#     ),
#     RParen(1:14:")"),
# )
# 
# (x: T1, y: T2,)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(
#         RecordTypeField(
#             LowerId(1:2:"x"),
#             Colon(1:3:":"),
#             Type_(NamedType(UpperId(1:5:"T1"))),
#         ),
#         Comma(1:7:","),
#         RecordTypeField(
#             LowerId(1:9:"y"),
#             Colon(1:10:":"),
#             Type_(NamedType(UpperId(1:12:"T2"))),
#         ),
#         Comma(1:14:","),
#     ),
#     RParen(1:15:")"),
# )
# 
# (x: T1, y: T2, ..r)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeFields(
#         RecordTypeField(
#             LowerId(1:2:"x"),
#             Colon(1:3:":"),
#             Type_(NamedType(UpperId(1:5:"T1"))),
#         ),
#         Comma(1:7:","),
#         RecordTypeField(
#             LowerId(1:9:"y"),
#             Colon(1:10:":"),
#             Type_(NamedType(UpperId(1:12:"T2"))),
#         ),
#         Comma(1:14:","),
#         DotDot(1:16:".."),
#         LowerId(1:18:"r"),
#     ),
#     RParen(1:19:")"),
# )
# 
# []
# Type_(LBracket(1:1:"["), RBracket(1:2:"]"))
# 
# [A]
# Type_(LBracket(1:1:"["), VariantAlt(UpperId(1:2:"A")), RBracket(1:3:"]"))
# 
# [A, B]
# Type_(
#     LBracket(1:1:"["),
#     VariantAlt(UpperId(1:2:"A")),
#     Comma(1:3:","),
#     VariantAlt(UpperId(1:5:"B")),
#     RBracket(1:6:"]"),
# )
# 
# [A, B,]
# Type_(
#     LBracket(1:1:"["),
#     VariantAlt(UpperId(1:2:"A")),
#     Comma(1:3:","),
#     VariantAlt(UpperId(1:5:"B")),
#     Comma(1:6:","),
#     RBracket(1:7:"]"),
# )
# 
# [A, B, ..foo]
# Type_(
#     LBracket(1:1:"["),
#     VariantAlt(UpperId(1:2:"A")),
#     Comma(1:3:","),
#     VariantAlt(UpperId(1:5:"B")),
#     Comma(1:6:","),
#     DotDot(1:8:".."),
#     LowerId(1:10:"foo"),
#     RBracket(1:13:"]"),
# )
# 
# Fn()
# Type_(UpperFn(1:1:"Fn"), LParen(1:3:"("), RParen(1:4:")"))
# 
# Fn(): Foo
# Type_(
#     UpperFn(1:1:"Fn"),
#     LParen(1:3:"("),
#     RParen(1:4:")"),
#     ReturnType(Colon(1:5:":"), Type_(NamedType(UpperId(1:7:"Foo")))),
# )
# 
# Fn(): exn Foo
# Type_(
#     UpperFn(1:1:"Fn"),
#     LParen(1:3:"("),
#     RParen(1:4:")"),
#     ReturnType(
#         Colon(1:5:":"),
#         Type_(LowerId(1:7:"exn")),
#         Type_(NamedType(UpperId(1:11:"Foo"))),
#     ),
# )
# 
# Fn(self)
# Type_(
#     UpperFn(1:1:"Fn"),
#     LParen(1:3:"("),
#     FnArgs(Param(Self(1:4:"self"))),
#     RParen(1:8:")"),
# )
# 
# Fn(self, a: U32): [] Foo
# Type_(
#     UpperFn(1:1:"Fn"),
#     LParen(1:3:"("),
#     FnArgs(
#         Param(Self(1:4:"self")),
#         Comma(1:8:","),
#         Param(
#             LowerId(1:10:"a"),
#             Colon(1:11:":"),
#             Type_(NamedType(UpperId(1:13:"U32"))),
#         ),
#     ),
#     RParen(1:16:")"),
#     ReturnType(
#         Colon(1:17:":"),
#         Type_(LBracket(1:19:"["), RBracket(1:20:"]")),
#         Type_(NamedType(UpperId(1:22:"Foo"))),
#     ),
# )

# expected stderr: compiler/Token.fir:138:9: Unexhaustive pattern match
