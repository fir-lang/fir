import Grammar
import Lexer
import PegTestLib


main(args: Array[Str]):
    runTopDecl("\
import Foo")
    runTopDecl("\
import Foo.Bar")
    runTopDecl("\
import Foo.Bar.Baz")


runTopDecl(input: Str):
    runTestScanner_(input, topDecl)

# expected stdout:
# import Foo
# TopDecl(ImportDecl(Import(1:1:"import"), UpperId(1:8:"Foo")))
# 
# import Foo.Bar
# TopDecl(
#     ImportDecl(Import(1:1:"import"), UpperId(1:8:"Foo"), UpperId(1:12:"Bar")),
# )
# 
# import Foo.Bar.Baz
# TopDecl(
#     ImportDecl(
#         Import(1:1:"import"),
#         UpperId(1:8:"Foo"),
#         UpperId(1:12:"Bar"),
#         UpperId(1:16:"Baz"),
#     ),
# )
