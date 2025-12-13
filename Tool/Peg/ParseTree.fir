type ParseTree[t, nt]:
    Terminal(t)

    NonTerminal(
        kind: nt,
        nodes: Vec[ParseTree[t, nt]],
    )


# Indicates an unexpected token (when `cursor` is smaller than the length of the input) or
# unexpected end-of-input (when `cursor` is the length of the input).
type ParseError(
    cursor: U32,
)


ParseError.takeAdvanced(err1: Option[ParseError], err2: ParseError) ParseError:
    match err1:
        Option.None: err2
        Option.Some(err1):
            if err1.cursor > err2.cursor:
                return err1
            else:
                return err2


ParseError.takeAdvancedOpt(err1: Option[ParseError], err2: Option[ParseError]) Option[ParseError]:
    match (left = err1, right = err2):
        (left = Option.Some(err1_), right = Option.Some(err2_)):
            if err1_.cursor > err2_.cursor:
                err1
            else:
                err2

        (left = Option.Some(_), ..): err1

        _: err2


impl[ToStr[t], ToStr[nt]] ToStr[ParseTree[t, nt]]:
    toStr(self: ParseTree[t, nt]) Str:
        self.toDoc().render(80)


impl ToStr[ParseError]:
    toStr(self: ParseError) Str:
        "unexpected token or end of input at cursor `self.cursor`"


ParseTree.toDoc[ToStr[t], ToStr[nt]](self: ParseTree[t, nt]) Doc:
    match self:
        ParseTree.Terminal(t): Doc.str(t.toStr())

        ParseTree.NonTerminal(kind, nodes):
            if nodes.len() == 0:
                return Doc.str(kind.toStr())

            let doc = Doc.str(kind.toStr()) + Doc.char('(') + Doc.break_(0)
            let nodeIdx: U32 = 0
            for node: ParseTree[t, nt] in nodes.iter():
                if nodeIdx != 0:
                    doc += Doc.char(',') + Doc.break_(1)
                doc += node.toDoc()
                nodeIdx += 1

            # Add a trailing comma when splitting the node list into lines.
            doc += Doc.whenNotFlat(Doc.char(','))

            (doc.nest(4) + Doc.break_(0) + Doc.char(')')).group()


ParseTree.asTerminal(self: ParseTree[t, nt]) t:
    match self:
        ParseTree.Terminal(t): t
        ParseTree.NonTerminal(..):
            panic("ParseTree.asTerminal: tree is a non-terminal")


ParseTree.asNonTerminal[Eq[nt], ToStr[nt]](self: ParseTree[t, nt], kind_: nt) Vec[ParseTree[t, nt]]:
    match self:
        ParseTree.Terminal(_):
            panic("ParseTree.asNonTerminal: tree is a terminal")
        ParseTree.NonTerminal(kind, nodes):
            if kind != kind_:
                panic("ParseTree.asNonTerminal: expected `kind_`, found `kind`")
            nodes


# --------------------------------------------------------------------------------------------------


## This trait used by the PEG runtime library (below) to skip tokens that the
## generated parsers don't care about.
trait TriviaTokens[t]:
    ## Whether the parser should ignore the token.
    isTrivia(self: t) Bool


type ParserState[t](
    _tokens: Array[t],
    _cursor: U32,
    _errorCursor: Option[U32],
)


impl Clone[ParserState[t]]:
    clone(self: ParserState[t]) ParserState[t]:
        ParserState(
            _tokens = self._tokens,
            _cursor = self._cursor,
            _errorCursor = self._errorCursor,
        )


ParserState.cloneFrom(self: ParserState[t], other: ParserState[t]):
    self._tokens = other._tokens
    self._cursor = other._cursor
    self._errorCursor = other._errorCursor


ParserState.new(tokens: Array[t]) ParserState[t]:
    ParserState(_tokens = tokens, _cursor = 0, _errorCursor = Option.None,)


## Whether the whole input is consumed.
ParserState.allConsumed(self: ParserState[t]) Bool:
    self._tokens.len() == self._cursor


## Returns the most advanced cursor in which an unexpected token was found.
##
## The cursor can point to the end of the input, which means an unexpected end-of-file was found.
ParserState.getErrorCursor(self: ParserState[t]) Option[U32]:
    self._errorCursor


## For generated code.
ParserState.peek[TriviaTokens[t]](self: ParserState[t]) Option[t]:
    loop:
        match self._tokens.getOpt(self._cursor):
            Option.Some(t) if t.isTrivia():
                self._cursor += 1
                continue

            other: return other

    panic("unreachable")


## For generated code.
ParserState.updateErrorCursor(self: ParserState[t], newErrorCursor: U32) U32:
    match self._errorCursor:
        Option.None:
            self._errorCursor = Option.Some(newErrorCursor)
            newErrorCursor
        Option.Some(err):
            if newErrorCursor > err:
                self._errorCursor = Option.Some(newErrorCursor)
                newErrorCursor
            else:
                err


## For generated code.
ParserState.nextCursor[TriviaTokens[t]](self: ParserState[t]) U32:
    self.peek()
    self._cursor
