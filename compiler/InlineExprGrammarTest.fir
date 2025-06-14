import InlineExprGrammar
import Lexer
import PegTestLib

main(args: Array[Str]):
    runTest_("1", inlineExpr)
    runTest_("1 + 2", inlineExpr)
    runTest_("1 + 2 - 3", inlineExpr)
    runTest_("Doc.str", inlineExpr)
    runTest_("Doc.str(\"hi\")", inlineExpr)
    runTest_("Doc.str(\"a\") + Doc.str(\"b\")", inlineExpr)
    ()
