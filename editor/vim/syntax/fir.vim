syntax case match

syntax keyword firKeyword
    \ elif
    \ else
    \ fn
    \ for
    \ if
    \ impl
    \ in
    \ let
    \ match
    \ return
    \ self
    \ trait
    \ type
    \ var
    \ while

syntax region firLineComment start="--" end="$"  contains=@Spell

syntax match firDecNumber display "[0-9][0-9_]*"

highlight default link firDecNumber firNumber

syntax region firString matchgroup=firStringDelimiter start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=@Spell

syntax match firType "\<[A-Z][a-zA-Z0-9_']*\>"

highlight default link firKeyword Keyword
highlight default link firLineComment Comment
highlight default link firNumber Number
highlight default link firStringDelimiter String
highlight default link firString String
highlight default link firType Type
