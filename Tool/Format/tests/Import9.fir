import [
    SomeModule/SubMod/[veryLongName1, veryLongName2, veryLongName3, veryLongName4],
]

# expected stdout:
# import [
#     SomeModule/SubMod/[
#         veryLongName1,
#         veryLongName2,
#         veryLongName3,
#         veryLongName4,
#     ],
# ]
