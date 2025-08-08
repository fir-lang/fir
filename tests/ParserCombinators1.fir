type ParseError:
    EndOfInput
    UnexpectedToken

impl ToStr[ParseError]:
    toStr(self: ParseError) Str:
        match self:
            ParseError.EndOfInput: "end of input"
            ParseError.UnexpectedToken: "unexpected token"

type Parser[input, output](
    f: Fn(Vec[input], U32) (output: output, nextPos: U32) / ParseError,
)

## Match a single token in the input.
Parser.match_(f: Fn(input) Option[output] / ParseError) Parser[input, output]:
    Parser(f = |input, pos|:
        if pos >= input.len():
            throw(ParseError.EndOfInput)
        match f(input.get(pos)):
            Option.None:
                throw(ParseError.UnexpectedToken)
            Option.Some(output):
                (output = output, nextPos = pos + 1))

## Match a character in the input.
Parser.char(c: Char) Parser[Char, ()]:
    Parser.match_(|input|:
        if input == c:
            Option.Some(())
        else:
            Option.None)

## Make the parser optional.
Parser.opt(self: Parser[input, output]) Parser[input, Option[output]]:
    Parser(f = |input, pos|:
        match try(||: self.f(input, pos)):
            Result.Ok((output, nextPos)):
                (output = Option.Some(output), nextPos = nextPos)
            Result.Err(_):
                (output = Option.None, nextPos = pos))


## Parse `p2` after `self`, return outputs of both.
Parser.seq(self: Parser[input, output1], p2: Parser[input, output2]) Parser[input, (first: output1, second: output2)]:
    Parser(f = |input, pos|:
        let res1 = self.f(input, pos)
        let res2 = p2.f(input, res1.nextPos)
        (output = (first = res1.output, second = res2.output), nextPos = res2.nextPos))

## Parse `self`, if fails, parse `p2`.
Parser.alt(self: Parser[input, output], p2: Parser[input, output]) Parser[input, output]:
    Parser(f = |input, pos|:
        match try(||: self.f(input, pos)):
            Result.Ok(res): res
            Result.Err(_): p2.f(input, pos))

Parser.parse(self: Parser[input, output], input: Vec[input]) (output: output, nextPos: U32) / ParseError:
    self.f(input, 0)

strToVec(s: Str) Vec[Char]:
    let chars: Vec[Char] = Vec.withCapacity(s.len())
    for c: Char in s.chars():
        chars.push(c)
    chars

main():
    let a = Parser.char('a')
    print(try(||: a.parse(strToVec("a")).output))
    print(try(||: a.parse(strToVec("b")).output))

    print("---")
    let seq = Parser.char('a').seq(Parser.char('b'))
    match try(||: seq.parse(strToVec("ab")).output):
        Result.Ok(_): print("OK")
        Result.Err(err): print(err)
    match try(||: seq.parse(strToVec("ac")).output):
        Result.Ok(_): print("OK")
        Result.Err(err): print(err)
    match try(||: seq.parse(strToVec("a")).output):
        Result.Ok(_): print("OK")
        Result.Err(err): print(err)

    print("---")
    let alt = Parser.char('a').alt(Parser.char('b'))
    print(try(||: alt.parse(strToVec("a")).output))
    print(try(||: alt.parse(strToVec("b")).output))
    print(try(||: alt.parse(strToVec("c")).output))

# expected stdout:
# Result.Ok(())
# Result.Err(unexpected token)
# ---
# OK
# unexpected token
# end of input
# ---
# Result.Ok(())
# Result.Ok(())
# Result.Err(unexpected token)
