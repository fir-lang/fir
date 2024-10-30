type Loc:
    # 0-based line number.
    line: U32

    # 0-based charcter number in the line.
    char: U32

    # Byte index of the location.
    byteIdx: U32

type LexerCommon[S]:
    # Current lexer state.
    _state: U32

    # Set after end-of-input is handled by a rule.
    #
    # Note: The initial rule (`Init`) handles end-of-input by default.
    _done: Bool

    # Which lexer state to switch to on successful match.
    _initialState: U32

    _userState: S

    _input: Str

    _iter: CharIter

    _peeked: Option[Option[Char]]

    # Start of the current match.
    _currentMatchStart: Loc

    # End of the current match.
    _currentMatchEnd: Loc

    # If we skipped an aaccepting state, this holds:
    #
    # - Skipped match start as byte index in `_input`.
    # - Semantic action function.
    # - Skipped match end as byte index in `_input`. (exclusive)
    _lastMatch: Option[()]  # TODO
