scan(tokens: Vec[Token]): Vec[Token]
    if tokens.len() == 0:
        return tokens

    # Somewhat random: assume an indentation token generated for every 6 tokens.
    # We should tweak this more based on code in the compiler and standard libraries.
    let newTokens: Vec[Token] = Vec.withCapacity(tokens.len() + tokens.len() / 6)

    let indentStack: Vec[U32] = Vec.withCapacity(10)

    # TODO

    newTokens
