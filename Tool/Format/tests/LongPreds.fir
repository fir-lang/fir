impl[ToDoc[RecRowList[VarExt[exts]]], ToDoc[RecRowList[AppExt[exts]]], ToDoc[RecRowList[AbsExt[exts]]], ToDoc[RecRowList[LetExt[exts]]]] ToDoc[Expr[exts]]:
    toDoc(self: Expr[exts]) Doc:
        ()

# expected stdout:
# impl[
#     ToDoc[RecRowList[VarExt[exts]]],
#     ToDoc[RecRowList[AppExt[exts]]],
#     ToDoc[RecRowList[AbsExt[exts]]],
#     ToDoc[RecRowList[LetExt[exts]]],
# ] ToDoc[Expr[exts]]:
#     toDoc(self: Expr[exts]) Doc:
#         ()
