import InlineExprGrammar
import Lexer
import PegTestLib

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

    ()
