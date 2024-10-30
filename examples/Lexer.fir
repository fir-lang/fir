type Token:
    LParen
    RParen
    Id(Str)
    String(Str)

type LexerState:
    comentDepth: U32

#|
Defines type:

... TODO
|#
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

        ['a'-'z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*: Token.Id(lexeme())

        ['0'-'9']+:
            match I64.fromStr(lexeme()):
                Result.Ok(i): Ok(Token.Int(i))
                Result.Err(_): Err(LexErr.InvalidInt(found = lexeme()))

        ['0'-'9']+ '.' ['0'-'9']*:
            match F64.fromStr(lexeme()):
                Result.Ok(f): Ok(Token.Float(f))
                Result.Err(_): Err(LexErr.InvalidFloat(found = lexeme()))

        "(*":
            state().comment_depth = 1
            switch(Comment)

    rule Comment:
        "(*":
            state().commentDepth += 1

        "*)":
            if state().commentDepth == 1:
                switch(Init)
            else:
                state().commentDepth -= 1

        _: continue

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


Type-checking rule RHSs:

- Each RHS will either return a token with the `return` keyword, or implicitly continue.
|#
