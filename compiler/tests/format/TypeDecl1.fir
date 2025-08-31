# Below we want one empty line between the fields.

type IntExpr(
    ## Blah blah blah
    text: Str,

    ## Blah blah
    suffix: Option[IntKind],

    ## Blah
    radix: U32,
)

# expected stdout:
# # Below we want one empty line between the fields.
# type IntExpr(
#     ## Blah blah blah
#     text: Str,
#     
#     ## Blah blah
#     suffix: Option[IntKind],
#     
#     ## Blah
#     radix: U32,
# )
