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

# expected stderr: compiler/Token.fir:138:9: Unexhaustive pattern match
