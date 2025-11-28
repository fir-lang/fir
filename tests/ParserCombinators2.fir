type ParseError:
    EndOfInput
    UnexpectedToken

impl ToStr[ParseError]:
    toStr(self: ParseError) Str:
        match self:
            ParseError.EndOfInput: "end of input"
            ParseError.UnexpectedToken: "unexpected token"

type Parser[input, output](
    f: Fn(ParserState[input]) output / ParseError,
)

type ParserState[input](
    input: Vec[input],
    pos: U32,
)

Parser.match_(f: Fn(input) output / ParseError) Parser[input, output]:
    Parser(f = \(state):
        if state.pos >= state.input.len():
            throw(ParseError.EndOfInput)
        let output = f(state.input.get(state.pos))
        state.pos += 1
        output)

Parser.char(c: Char) Parser[Char, ()]:
    Parser.match_(\(c_):
        if c != c_:
            throw(ParseError.UnexpectedToken))

Parser.seq(self: Parser[input, output], cont: Fn(output) Parser[input, output] / ParseError) Parser[input, output]:
    Parser(f = \(state): cont(self.f(state)).f(state))

Parser.opt(self: Parser[input, output]) Parser[input, Option[output]]:
    Parser(f = \(state):
        let pos0 = state.pos
        match try(\(): self.f(state)):
            Result.Err(_):
                state.pos = pos0
                Option.None
            Result.Ok(val):
                Option.Some(val))

Parser.alt(self: Parser[input, output], p2: Parser[input, output]) Parser[input, output]:
    Parser(f = \(state):
        let pos0 = state.pos
        match try(\(): self.f(state)):
            Result.Ok(res):
                res
            Result.Err(_):
                state.pos = pos0
                p2.f(state))

Parser.parse(self: Parser[input, output], input: Vec[input]) output / ParseError:
    let state = ParserState(input, pos = 0)
    self.f(state)

strToVec(s: Str) Vec[Char]:
    let chars: Vec[Char] = Vec.withCapacity(s.len())
    for c: Char in s.chars():
        chars.push(c)
    chars

main():
    let a = Parser.char('a')
    print(try(\(): a.parse(strToVec("a"))))
    print(try(\(): a.parse(strToVec("b"))))

    print("---")
    let seq = Parser.char('a').seq(\(_x): Parser.char('b'))
    print(try(\(): seq.parse(strToVec("ab"))))
    print(try(\(): seq.parse(strToVec("ac"))))
    print(try(\(): seq.parse(strToVec("a"))))

    print("---")
    let alt = Parser.char('a').alt(Parser.char('b'))
    print(try(\(): alt.parse(strToVec("a"))))
    print(try(\(): alt.parse(strToVec("b"))))
    print(try(\(): alt.parse(strToVec("c"))))

# expected stdout:
# Result.Ok(())
# Result.Err(unexpected token)
# ---
# Result.Ok(())
# Result.Err(unexpected token)
# Result.Err(end of input)
# ---
# Result.Ok(())
# Result.Ok(())
# Result.Err(unexpected token)
