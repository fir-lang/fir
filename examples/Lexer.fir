type Token:
    LParen
    RParen
    Id(Str)
    String(Str)

type LexerState:
    comentDepth: U32

fn t[E](token: Token): Result[E, Token] =
    Result.Ok(token)

lexer Lexer:
    rule Init:
        [' ' '\t' '\n']+: t(Token.Whitespace)

        "(": t(Token.LParen)
        ")": t(Token.RParen)
        "true": t(Token.Bool(true))
        "false": t(Token.Bool(false))
        "not": t(Token.Not)
        "if": t(Token.If)
        "then": t(Token.Then)
        "else": t(Token.Else)
        "let": t(Token.Let)
        "rec": t(Token.Rec)
        "in": t(Token.In)
        "-": t(Token.Minus)
        "-.": t(Token.MinusDot)
        "+": t(Token.Plus)
        "+.": t(Token.PlusDot)
        "*.": t(Token.AstDot)
        "/.": t(Token.SlashDot)
        "=": t(Token.Equal)
        "<>": t(Token.LessGreater)
        "<=": t(Token.LessEqual)
        "<-": t(Token.LessMinus)
        "<": t(Token.Less)
        ">=": t(Token.GreaterEqual)
        ">": t(Token.Greater)
        ".": t(Token.Dot)
        ",": t(Token.Comma)
        ";": t(Token.Semicolon)
        "_": t(Token.Underscore)
        "Array.create": t(Token.ArrayCreate)
        "Array.make": t(Token.ArrayCreate)

        ['a'-'z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*: t(Token.Id(lexeme()))

        ['0'-'9']+:
            match I32.fromStr(lexeme()):
                Result.Ok(i): Result.Ok(Token.Int(i))
                Result.Err(_): Result.Err(LexErr.InvalidInt(found = lexeme()))

        # ['0'-'9']+ '.' ['0'-'9']*:
        #     match F64.fromStr(lexeme()):
        #         Result.Ok(f): Result.Ok(Token.Float(f))
        #         Result.Err(_): Result.Err(LexErr.InvalidFloat(found = lexeme()))

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
