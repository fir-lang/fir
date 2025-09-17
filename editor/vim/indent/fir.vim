if exists('b:did_indent')
  finish
endif
let b:did_indent = 1

setlocal autoindent

setlocal indentexpr=FirIndent()

if exists('*FirIndent')
  finish
endif

function! FirIndent()
  " By default use the previous line's indentation.
  let indentTo = indent(v:lnum)

  " Indent after ':' and '=' unless in a comment.
  let previousNonBlankLine = prevnonblank(v:lnum - 1)
  let previousLine = getline(previousNonBlankLine)

  " Get the syntax ID of the first non-blank character of the previous line.
  let synID = synID(previousNonBlankLine, col([previousNonBlankLine, '$']) - strlen(previousLine) + 1, 1)
  let synName = synIDattr(synID, 'name')

  if synName =~? 'comment'
    " If the previous line is a comment, use its indentation level.
    let indentTo = indent(previousNonBlankLine)
  elseif previousLine =~# '[:=([{]$'
    let indentTo = indent(previousNonBlankLine) + &shiftwidth
  endif

  return indentTo
endfunction
