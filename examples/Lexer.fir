type Token:
    LParen
    RParen
    Id(Str)
    String(Str)

type LexerState:
    comentDepth: U32

lexer Lexer:
    rule Init:
        [' ' '\t' '\n']+: Token.Whitespace

        "(": Token.LParen
        ")": Token.RParen
        "true": Token.Bool(true)
        "false": Token.Bool(false)
        "not": Token.Not
        "if": Token.If
        "then": Token.Then
        "else": Token.Else
        "let": Token.Let
        "rec": Token.Rec
        "in": Token.In
        "-": Token.Minus
        "-.": Token.MinusDot
        "+": Token.Plus
        "+.": Token.PlusDot
        "*.": Token.AstDot
        "/.": Token.SlashDot
        "=": Token.Equal
        "<>": Token.LessGreater
        "<=": Token.LessEqual
        "<-": Token.LessMinus
        "<": Token.Less
        ">=": Token.GreaterEqual
        ">": Token.Greater
        ".": Token.Dot
        ",": Token.Comma
        ";": Token.Semicolon
        "_": Token.Underscore
        "Array.create": Token.ArrayCreate
        "Array.make": Token.ArrayCreate

        ['a'-'z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*:
            return Token.Id(lexeme())

        ['0'-'9']+:
            match I64.fromStr(lexeme()):
                Ok(i):
                    return Ok(Token.Int(i))
                Err(_):
                    return Err(LexErr.InvalidInt(found = lexeme()))

        ['0'-'9']+ '.' ['0'-'9']*:
            match F64.fromStr(lexeme()):
                Ok(f):
                    return Ok(Token.Float(f))
                Err(_):
                    return Err(LexErr.InvalidFloat(found = lexeme()))

        "(*":
            state().comment_depth = 1
            switch(Comment)


#|
Syntax for lexer actions:

return: use the `return` keyword
continue: use the `continue` keyword. When in a loop, use `continue LexerName`.
switch: add contextual `switch` keyword
    For now: switch function, as it's not easy to add contextual keywords, see
    https://github.com/lalrpop/lalrpop/issues/966

Also:

Get current match: lexeme() built-in function
Peek: peek() built-in function
Reset current match: resetMatch() built-in function
Get lexer state: lexer() built-in function. (or variable?)
|#
