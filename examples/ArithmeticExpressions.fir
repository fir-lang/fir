# An implementation of the "Untyped Arithmetic Expressions" language described in Types and
# Programming Languages section 3.

import Prelude

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
                    panic("If condition evaluated to number $(i)")

        Term.Zero: Value.Num(0)

        Term.Succ(term):
            match eval(term):
                Value.Bool(bool): panic("Succ argument evaluated to bool $(bool)")
                Value.Num(value): Value.Num(value + 1)

        Term.Pred(term):
            match eval(term):
                Value.Bool(bool): panic("Pred argument evaluated to bool $(bool)")
                Value.Num(value): Value.Num(value - 1)

        Term.IsZero(term):
            match eval(term):
                Value.Bool(bool): panic("IsZero argument evaluated to bool $(bool)")
                Value.Num(value): Value.Bool(value == 0)

fn Value.toStr(self): Str =
    match self:
        Value.Bool(value): value.toStr()
        Value.Num(value): value.toStr()

fn parse(pgm: StrView): Term =
    let (term = term, rest = rest) = parseWithRest(pgm)
    if !rest.isEmpty():
        panic("Leftover code after parsing the program: \"$(rest)\"")
    term

fn skipWhitespace(pgm: StrView): StrView =
    while pgm.len() > 0 && pgm.substr(0, 1) == " ".substr(0, 1):
        pgm = pgm.substr(1, pgm.len())
    pgm

## Parse the program, return the parsed term and the unparsed part of the program.
fn parseWithRest(pgm: StrView): (term: Term, rest: StrView) =
    let pgm = skipWhitespace(pgm)

    match pgm:
        "0" rest:
            return (term = Term.Zero, rest = rest)
        "true" rest:
            return (term = Term.True, rest = rest)
        "false" rest:
            return (term = Term.False, rest = rest)
        "succ" rest:
            let (arg = arg, rest = rest) = parseArg(rest)
            return (term = Term.Succ(arg), rest = rest)
        "pred" rest:
            let (arg = arg, rest = rest) = parseArg(rest)
            return (term = Term.Pred(arg), rest = rest)
        "iszero" rest:
            let (arg = arg, rest = rest) = parseArg(rest)
            return (term = Term.IsZero(arg), rest = rest)
        _:
            panic("Invalid syntax: \"$(pgm)\"")

fn parseArg(pgm: StrView): (arg: Term, rest: StrView) =
    # Skip "("
    if pgm.isEmpty() || pgm.substr(0, 1) != "(".substr(0, 1):
        panic("Unexpected end of program while parsing arguments")

    let pgm = pgm.substr(1, pgm.len())

    # Parse argument
    let (term = arg, rest = rest)  = parseWithRest(pgm)

    # Skip ")"
    if rest.isEmpty() || rest.substr(0, 1) != ")".substr(0, 1):
        panic("Unexpected end of program while parsing arguments")
    let rest = rest.substr(1, rest.len())

    (arg = arg, rest = rest)
