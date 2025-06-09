syntax case match

syntax keyword firKeyword
    \ and
    \ as
    \ break
    \ continue
    \ elif
    \ else
    \ export
    \ fn
    \ Fn
    \ for
    \ if
    \ impl
    \ import
    \ in
    \ is
    \ jump
    \ let
    \ loop
    \ match
    \ not
    \ or
    \ prim
    \ return
    \ trait
    \ type
    \ var
    \ while

syntax region firLineComment start="#" end="$"  contains=@Spell

syntax match firNumber display "\<\(0x\|0X\|0b\|0B\)\?[a-fA-F0-9][a-fA-F0-9_]*\(u8\|u16\|u32\|u64\|i8\|i16\|i32\|i64\)\?\>"

syntax match firType "\<_\?[A-Z][a-zA-Z0-9_']*\>"

syntax match firVariable "\<_\?[a-z][a-zA-Z0-9_']*\>"

syntax cluster firStringContains contains=firInterpolation
syntax region firString matchgroup=firStringDelimiter start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=@Spell,@firStringContains
syntax region firChar start=+'+ skip=+\\\\\|\\'+ end=+'+
syntax match firInterpolation contained "`\([^`]\+\)`" extend

syntax match firParenStart "("
syntax match firParenEnd ")"
syntax match firBracketStart "\["
syntax match firBracketEnd "\]"
syntax match firBraceStart "{"
syntax match firBraceEnd "}"

syntax match firComma ","
syntax match firColon ":"

syn region firBlockComment start="#|" end="|#"
  \ contains=
  \ firBlockCommentBlockComment,
  \ firTodo,
  \ @Spell

syn keyword firTodo TODO FIXME BUG contained

syntax match firOperator "=\|==\|+=\|-=\|*=\|\^=\|+\|-\|*\|!\|&\|&&\||\|||\|<\|<<\|<=\|>\|>>\|>=\|!=\|/\|%\|\^\|\.\."

highlight default link firKeyword Keyword
highlight default link firLineComment Comment
highlight default link firNumber Number
highlight default link firStringDelimiter String
highlight default link firString String
highlight default link firChar Character
highlight default link firType Type
highlight default link firVariable Variable
highlight default link firBlockComment Comment
highlight default link firTodo Todo
highlight default link firOperator Operator
highlight default link firComma Delimiter
highlight default link firColon Delimiter
highlight default link firParenStart Delimiter
highlight default link firParenEnd Delimiter
highlight default link firBraceStart Delimiter
highlight default link firBraceEnd Delimiter
highlight default link firBracketStart Delimiter
highlight default link firBracketEnd Delimiter
