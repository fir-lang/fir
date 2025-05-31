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
#     RecordTypeField(Type_(LowerId(1:2:"a"))),
#     RParen(1:3:")"),
# )
# 
# (a, b)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeField(Type_(LowerId(1:2:"a"))),
#     Comma(1:3:","),
#     RecordTypeField(Type_(LowerId(1:5:"b"))),
#     RParen(1:6:")"),
# )
# 
# (x: T)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeField(
#         LowerId(1:2:"x"),
#         Colon(1:3:":"),
#         Type_(NamedType(UpperId(1:5:"T"))),
#     ),
#     RParen(1:6:")"),
# )
# 
# (x: T1, y: T2)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeField(
#         LowerId(1:2:"x"),
#         Colon(1:3:":"),
#         Type_(NamedType(UpperId(1:5:"T1"))),
#     ),
#     Comma(1:7:","),
#     RecordTypeField(
#         LowerId(1:9:"y"),
#         Colon(1:10:":"),
#         Type_(NamedType(UpperId(1:12:"T2"))),
#     ),
#     RParen(1:14:")"),
# )
# 
# (x: T1, y: T2, ..r)
# Type_(
#     LParen(1:1:"("),
#     RecordTypeField(
#         LowerId(1:2:"x"),
#         Colon(1:3:":"),
#         Type_(NamedType(UpperId(1:5:"T1"))),
#     ),
#     Comma(1:7:","),
#     RecordTypeField(
#         LowerId(1:9:"y"),
#         Colon(1:10:":"),
#         Type_(NamedType(UpperId(1:12:"T2"))),
#     ),
#     Comma(1:14:","),
#     Comma(1:14:","),
#     DotDot(1:16:".."),
#     LowerId(1:18:"r"),
#     RParen(1:19:")"),
# )

# expected stderr: compiler/Token.fir:138:9: Unexhaustive pattern match
