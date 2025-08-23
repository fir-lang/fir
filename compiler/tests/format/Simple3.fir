TypeDeclRhs.format(self, tokens: Vec[Token]) Doc:
    match self:
        TypeDeclRhs.Sum(decls):
            Doc.char(':')
                + Doc.hardLine()
                + join(decls.iter().map(||: decl.format(tokens)), Doc.hardLine())
                + Doc.hardLine()
        TypeDeclRhs.Product(fields):
            fields.format(tokens)

# expected stdout:
# TypeDeclRhs.format(self, tokens: Vec[Token]) Doc:
#     match self:
#         TypeDeclRhs.Sum(decls):
#             Doc.char(':')
#                 + Doc.hardLine()
#                 + join(
#                     decls.iter().map(||: decl.format(tokens)),
#                     Doc.hardLine(),
#                 )
#                 + Doc.hardLine()
#         TypeDeclRhs.Product(fields): fields.format(tokens)
