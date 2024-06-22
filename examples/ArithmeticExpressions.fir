-- An implementation of the "Untyped Arithmetic Expressions" language described in Types and
-- Programming Languages section 3.

-- Takes the program code as the first command line argument.

fn main(pgm: Str) =
    let pgmStringView = pgm.substr(0, pgm.len())
    printStr(eval(parse(pgmStringView)).toStr())

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

fn eval(term: Term): Value =
    match term:
        Term.True: Value.Bool(Bool.True)

        Term.False: Value.Bool(Bool.False)

        Term.If(cond, then, else_):
            match eval(cond):
                Value.Bool(b):
                    if b:
                        eval(then)
                    else:
                        eval(else_)
                Value.Num(i):
                    panic("If condition evaluated to number")

        Term.Zero: Value.Num(0)

        Term.Succ(term):
            match eval(term):
                Value.Bool(_): panic("Succ argument evaluated to bool")
                Value.Num(value): Value.Num(value + 1)

        Term.Pred(term):
            match eval(term):
                Value.Bool(_): panic("Pred argument evaluated to bool")
                Value.Num(value): Value.Num(value - 1)

        Term.IsZero(term):
            match eval(term):
                Value.Bool(_): panic("IsZero argument evaluated to bool")
                Value.Num(value): Value.Bool(value == 0)

fn Value.toStr(self): Str =
    match self:
        Value.Bool(value): value.toStr()
        Value.Num(value): value.toStr()

fn parse(pgm: StrView): Term =
    let termAndRest: (term: Term, rest: StrView) = parseWithRest(pgm)
    let term = termAndRest.term
    let rest = termAndRest.rest
    if !rest.isEmpty():
        printStrView(rest)
        panic()
    term

fn skipWhitespace(pgm: StrView): StrView =
    while pgm.len() > 0 && pgm.substr(0, 1) == " ".substr(0, 1):
        pgm = pgm.substr(1, pgm.len())
    pgm

-- | Parse the program, return the parsed term and the unparsed part of the program.
fn parseWithRest(pgm: StrView): (term: Term, rest: StrView) =
    let pgm = skipWhitespace(pgm)

    -- TODO: Implement pattern matching on strings.
    -- Bound variables should be stack allocated view objects.
    -- match pgm:
    --     "0" .. rest:
    --         return (term = Term.Zero, rest = pgm.substr(1, pgm.len()))
    --     "true" .. rest:
    --         return (term = Term.True, rest = pgm.substr(4, pgm.len()))
    --     "false" .. rest:
    --         return (term = Term.False, rest = pgm.substr(5, pgm.len()))
    --     "succ" .. rest:
    --         let (arg, rest) = parseArg(rest)
    --         return (term = Term.Succ(arg), rest = rest)
    --     "pred" .. rest:
    --         let (arg, rest) = parseArg(pgm)
    --         return (term = Term.Pred(arg), rest)
    --     "iszero" .. rest:
    --         let (arg, rest) = parseArg(pgm)
    --         return (term = Term.IsZero(arg), rest)

    if pgm.startsWith("0"):
        return (term = Term.Zero, rest = pgm.substr(1, pgm.len()))

    if pgm.startsWith("true"):
        return (term = Term.True, rest = pgm.substr(4, pgm.len()))

    if pgm.startsWith("false"):
        return (term = Term.False, rest = pgm.substr(5, pgm.len()))

    if pgm.startsWith("succ"):
        let pgm = pgm.substr(4, pgm.len())
        let argAndRest = parseArg(pgm)
        let arg = argAndRest.arg
        let rest = argAndRest.rest
        return (term = Term.Succ(arg), rest = rest)

    if pgm.startsWith("pred"):
        let pgm = pgm.substr(4, pgm.len())
        let argAndRest  = parseArg(pgm)
        let arg = argAndRest.arg
        let rest = argAndRest.rest
        return (term = Term.Pred(arg), rest = rest)

    if pgm.startsWith("iszero"):
        let pgm = pgm.substr(6, pgm.len())
        let argAndRest = parseArg(pgm)
        let arg = argAndRest.arg
        let rest = argAndRest.rest
        return (term = Term.IsZero(arg), rest = rest)

    panic()

fn parseArg(pgm: StrView): (arg: Term, rest: StrView) =
    -- Skip "("
    if pgm.isEmpty() || pgm.substr(0, 1) != "(".substr(0, 1):
        panic()

    let pgm: StrView = pgm.substr(1, pgm.len())

    -- Parse argument
    let termAndRest: (term: Term, rest: StrView) = parseWithRest(pgm)
    let arg = termAndRest.term
    let pgm = termAndRest.rest

    -- Skip ")"
    if pgm.isEmpty() || pgm.substr(0, 1) != ")".substr(0, 1):
        panic()
    let pgm = pgm.substr(1, pgm.len())

    (arg = arg, rest = pgm)

-- For now, this needs to be defined somewhere in the program. We will remove
-- this once we have a prelude.
type Ordering:
    Less
    Equal
    Greater
