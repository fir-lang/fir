# `Main` imports `Synonyms` (which exports `Bar`) but does NOT import `Lib`
# under any alias. When the synonym `Bar` gets expanded into `Main`'s function
# signatures, the substituted body still contains the literal `mod_prefix=Lib`
# from `Synonyms.fir`. That prefix isn't valid in `Main`'s env. Synonym
# expansion skips it gracefully, but monomorphisation still calls the panicking
# `module_env.resolve` and aborts:
#
#   :1:1: Unbound name Lib/Foo
#
# `--typecheck` alone passes; the panic only fires on the full-run path.

import [Tests/Modules/SynonymPrefixedBody/Synonyms]


useBar(b: Bar) U32:
    b.item


main():
    print(useBar(makeBar()))


# expected stdout: 7
