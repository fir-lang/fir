import Lexer
import PegGrammar
import Scanner
import Token

main()
    let contents = readFileUtf8("compiler/PegGrammar.peg")
    let (tokens, error) = tokenize("PegGrammar.peg", contents)
    if error is Option.Some(error):
        panic(errStr(error))
    let tokens = scan(tokens)
    match try({ terminalsDecl(tokens, 0) }):
        Result.Err(err): print(err)
        Result.Ok(result): print(result.tree.toDoc().print(80))

errStr(err: Error): Str
    "`err.loc.file`:`err.loc.line + 1`:`err.loc.col + 1`: `err.msg`"
