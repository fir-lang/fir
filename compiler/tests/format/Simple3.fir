# The line with `+ join(...)` ends at column 81, it should be broken down.

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
# # The line with `+ join(...)` ends at column 81, it should be broken down.
# TypeDeclRhs.format(self, tokens: Vec[Token]) Doc:
#     match self:
#         TypeDeclRhs.Sum(decls):
#             Doc.char(':')
#                 + Doc.hardLine()
#                 + join(decls.iter().map(||: decl.format(tokens)), Doc.hardLine())
#                 + Doc.hardLine()
#         TypeDeclRhs.Product(fields): fields.format(tokens)
