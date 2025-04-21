syntax case match

syntax keyword firKeyword
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
    \ jump
    \ let
    \ loop
    \ match
    \ prim
    \ return
    \ trait
    \ type
    \ var
    \ while

syntax region firLineComment start="#" end="$"  contains=@Spell

syntax match firDecNumber display "[0-9][0-9_]*"

highlight default link firDecNumber firNumber

syntax match firType "\<[A-Z][a-zA-Z0-9_']*\>"

syntax cluster firStringContains contains=firInterpolation
syntax region firString matchgroup=firStringDelimiter start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=@Spell,@firStringContains
syntax match firInterpolation contained "`\([^`]\+\)`" extend

syntax region firParen   transparent matchgroup=firParens   start='(' end=')'
syntax region firBracket transparent matchgroup=firBrackets start="\[" end="\]"
syntax region firBraces  transparent matchgroup=firBraces start="{" end="}"

syntax match firComma ","
syntax match firColon ":"

syn region firBlockComment start="#|" end="|#"
  \ contains=
  \ firBlockCommentBlockComment,
  \ firTodo,
  \ @Spell

syn keyword firTodo TODO FIXME BUG contained

syntax match firOperator "=\|==\|+=\|-=\|*=\|\^=\|+\|-\|*\|!\|&\|&&\||\|||\|<\|<<\|<=\|>\|>>\|>=\|!=\|/\|%\|\^"

highlight default link firKeyword Keyword
highlight default link firLineComment Comment
highlight default link firNumber Number
highlight default link firStringDelimiter String
highlight default link firString String
highlight default link firType Type
highlight default link firBrackets Delimiter
highlight default link firParens Delimiter
highlight default link firBraces Delimiter
highlight default link firBlockComment Comment
highlight default link firTodo Todo
highlight default link firOperator Operator
highlight default link firComma Delimiter
highlight default link firColon Delimiter
