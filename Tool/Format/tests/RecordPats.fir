impl Eq[TokenKind]:
    __eq(self: TokenKind, other: TokenKind) Bool:
        match (left = self, right = other):
            (left = TokenKind.Amp, right = TokenKind.Amp): Bool.True
            (left = TokenKind.DoubleLAngle, right = TokenKind.DoubleLAngle): Bool.True
            (left = TokenKind.TildeUpperIdPath, right = TokenKind.TildeUpperIdPath): Bool.True
            (left = TokenKind.TildeUpperIdPathLongLongLongLongLongLongLongLong, right = TokenKind.TildeUpperIdPathLong): Bool.True
            _: Bool.False

# expected stdout:
# impl Eq[TokenKind]:
#     __eq(self: TokenKind, other: TokenKind) Bool:
#         match (left = self, right = other):
#             (left = TokenKind.Amp, right = TokenKind.Amp): Bool.True
#             (left = TokenKind.DoubleLAngle, right = TokenKind.DoubleLAngle):
#                 Bool.True
#             (
#                 left = TokenKind.TildeUpperIdPath,
#                 right = TokenKind.TildeUpperIdPath,
#             ): Bool.True
#             (
#                 left =
#                     TokenKind.TildeUpperIdPathLongLongLongLongLongLongLongLong,
#                 right = TokenKind.TildeUpperIdPathLong,
#             ): Bool.True
#             _: Bool.False
