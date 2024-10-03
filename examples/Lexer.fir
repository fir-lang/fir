type Token:
    LParen
    RParen
    Id
    String

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
            let match_ = lexer.match_()
            return Token.Id(match_.to_owned())

        ['0'-'9']+:
            let match_ = lexer.match_()
            match I64.from_str(match_):
                Ok(i):
                    return Ok(Token::Int(i))
                Err(_):
                    return Err(LexErr::InvalidInt { found: match_.to_owned() })

        ['0'-'9']+ '.' ['0'-'9']*:
            let match_ = lexer.match_()
            match f64::from_str(match_):
                Ok(f):
                    return Ok(Token::Float(f))
                Err(_):
                    return Err(LexErr::InvalidFloat { found: match_.to_owned() })

        "(*":
            lexer.state().comment_depth = 1
            lexer.switch(LexerRule::Comment)


#|
Syntax for lexer actions:

return: use the `return` keyword
continue: use the `continue` keyword. When in a loop, use `continue LexerName`.
switch: add contextual `switch` keyword
switch_and_return: doesn't exist in Fir, use `switch` and then `return`.

Also:

Get current match:
Peek:
Reset current match:
|#


# This is a single line comment.

#:
    This is a multi-line comment.
    The comment ends with the indented block.

#:  You can also do this.
    Still a comment.
