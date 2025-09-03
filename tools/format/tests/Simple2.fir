main():
    if self.body is Option.Some(stmts):
        doc += Doc.nested(4, Doc.char(':') + Doc.hardLine() + formatStmts(stmts, tokens))

# expected stdout:
# main():
#     if self.body is Option.Some(stmts):
#         doc += Doc.nested(
#             4,
#             Doc.char(':') + Doc.hardLine() + formatStmts(stmts, tokens),
#         )
