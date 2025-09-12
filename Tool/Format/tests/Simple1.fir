ReturnExpr.format(self, tokens: Vec[Token]) Doc:
    match self.expr:
        Option.None: Doc.str("return")
        Option.Some(expr): Doc.nested(4, Doc.str("return") + Doc.break_(1) + expr.format(tokens)).group().group()

# expected stdout:
# ReturnExpr.format(self, tokens: Vec[Token]) Doc:
#     match self.expr:
#         Option.None: Doc.str("return")
#         Option.Some(expr):
#             Doc.nested(
#                 4,
#                 Doc.str("return") + Doc.break_(1) + expr.format(tokens),
#             ).group().group()
