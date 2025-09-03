topFunSig(state: ParserState[Token]) (parentTy: Option[Id], name: Id, sig: FunSig) / U32:
    1

# Right paren at column 81.
runParser(input: Str, parseFn: Fn(ParserState[Token]) tree / U32, runScan: Bool,) tree / TestError:
    ()

# expected stdout:
# topFunSig(state: ParserState[Token]) (parentTy: Option[Id], name: Id, sig: FunSig) / U32:
#     1
# 
# 
# # Right paren at column 81.
# runParser(
#     input: Str,
#     parseFn: Fn(ParserState[Token]) tree / U32,
#     runScan: Bool,
# ) tree / TestError:
#     ()
