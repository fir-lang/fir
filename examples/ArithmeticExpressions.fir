# An implementation of the "Untyped Arithmetic Expressions" language described in Types and
# Programming Languages section 3.

main(pgm: Str) = print(eval(parse(pgm)))

type Term:
    True

    False

    If:
        cond: Term
        then: Term
        else_: Term

    Zero

    Succ(Term)

    Pred(Term)

    IsZero(Term)

type Value:
    Bool(Bool)
    Num(I32)

eval(term: Term): Value
    match term:
        Term.True: Value.Bool(Bool.True)

        Term.False: Value.Bool(Bool.False)

        # TODO: Allow simplifying this as `Term.If(cond, then, else_)`.
        Term.If(cond = cond, then = then, else_ = else_):
            match eval(cond):
                Value.Bool(b):
                    if b:
                        eval(then)
                    else:
                        eval(else_)
                Value.Num(i):
                    panic("If condition evaluated to number `i`")

        Term.Zero: Value.Num(0)

        Term.Succ(term):
            match eval(term):
                Value.Bool(bool): panic("Succ argument evaluated to bool `bool`")
                Value.Num(value): Value.Num(value + 1)

        Term.Pred(term):
            match eval(term):
                Value.Bool(bool): panic("Pred argument evaluated to bool `bool`")
                Value.Num(value): Value.Num(value - 1)

        Term.IsZero(term):
            match eval(term):
                Value.Bool(bool): panic("IsZero argument evaluated to bool `bool`")
                Value.Num(value): Value.Bool(value == 0)

impl ToStr[Value]:
    toStr(self: Value): Str
        match self:
            Value.Bool(value): value.toStr()
            Value.Num(value): value.toStr()

parse(pgm: Str): Term
    let (term = term, rest = rest) = parseWithRest(pgm)
    if !rest.isEmpty():
        panic("Leftover code after parsing the program: \"`rest`\"")
    term

skipWhitespace(pgm: Str): Str
    while pgm.len() > 0 && pgm.startsWith(" "):
        pgm = pgm.substr(1, pgm.len())
    pgm

## Parse the program, return the parsed term and the unparsed part of the program.
parseWithRest(pgm: Str): (term: Term, rest: Str)
    match skipWhitespace(pgm):
        "0" rest:
            (term = Term.Zero, rest = rest)
        "true" rest:
            (term = Term.True, rest = rest)
        "false" rest:
            (term = Term.False, rest = rest)
        "succ" rest:
            let (arg = arg, rest = rest) = parseArg(rest)
            (term = Term.Succ(arg), rest = rest)
        "pred" rest:
            let (arg = arg, rest = rest) = parseArg(rest)
            (term = Term.Pred(arg), rest = rest)
        "iszero" rest:
            let (arg = arg, rest = rest) = parseArg(rest)
            (term = Term.IsZero(arg), rest = rest)
        "if" rest:
            let (term = cond, rest = rest) = parseWithRest(rest)
            let rest = expectKeyword(rest, "then")
            let (term = then, rest = rest) = parseWithRest(rest)
            let rest = expectKeyword(rest, "else")
            let (term = else_, rest = rest) = parseWithRest(rest)
            (term = Term.If(cond = cond, then = then, else_ = else_), rest = rest)
        _:
            panic("Invalid syntax: \"`pgm`\"")

parseArg(pgm: Str): (arg: Term, rest: Str)
    # Skip "("
    if pgm.isEmpty():
        panic("Unexpected end of program while parsing arguments")

    if !pgm.startsWith("("):
        panic("Missing argument list")

    let pgm = pgm.substr(1, pgm.len())

    # Parse argument
    let (term = arg, rest = rest)  = parseWithRest(pgm)

    # Skip ")"
    if rest.isEmpty():
        panic("Unexpected end of program while parsing arguments")

    if !rest.startsWith(")"):
        panic("Missing ')'")

    let rest = rest.substr(1, rest.len())

    (arg = arg, rest = rest)

expectKeyword(pgm: Str, kw: Str): Str
    let pgm = skipWhitespace(pgm)
    if !pgm.startsWith(kw.toStr()):
        panic("Expected \"`kw`\", found \"`pgm`\"")
    pgm.substr(kw.len(), pgm.len())

testMain(): [] ()
    main("0")
    main("succ(0)")
    main("succ(succ(0))")
    main("succ(pred(succ(0)))")
    main("pred(succ(pred(succ(0))))")
    main("if true then succ(0) else 0")
    main("if iszero(0) then succ(0) else 0")

# args: --main testMain
# expected stdout:
# 0
# 1
# 2
# 1
# 0
# 1
# 1
