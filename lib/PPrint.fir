## Fir port of OCaml's PPrint[1].
##
## [1]: https://github.com/fpottier/pprint

type Doc:
    _Empty

    _Str(
        str: Str,
        lenChars: U32,
    )

    _Blank(spaces: U32)

    _IfFlat(
        flat: Doc,
        notFlat: Doc,
    )

    _HardLine

    _Cat(
        req: _SpaceReq,
        doc1: Doc,
        doc2: Doc,
    )

    _Nest(
        req: _SpaceReq,
        indent: U32,
        doc: Doc,
    )

    _Group(
        req: _SpaceReq,
        doc: Doc,
    )

type _State(
    width: U32,
    column: U32,
    output: StrBuf,
)

Doc.render(self, width: U32) Str:
    # TODO: For now copying the initial buffer size from the original PPrint, but we should be able
    # to estimate better numbers using the `Doc` type.
    let output = StrBuf.withCapacity(512)
    self.renderToBuf(width, output)
    output.toStr()

Doc.renderToBuf(self, width: U32, buf: StrBuf):
    let state = _State(width, column = 0, output = buf)
    self._render(state, 0, Bool.False)

Doc._render(self, state: _State, indent: U32, flatten: Bool):
    match self:
        Doc._Empty: ()

        Doc._Str(str, lenChars):
            state.output.pushStr(str)
            state.column += lenChars

        Doc._Blank(spaces):
            for _: U32 in range(u32(0), spaces):
                state.output.push(' ')
            state.column += spaces

        Doc._HardLine:
            if flatten:
                panic("")
            state.output.push('\n')
            for _: U32 in range(u32(0), indent):
                state.output.push(' ')
            state.column = indent

        Doc._IfFlat(flat, notFlat):
            if flatten:
                flat._render(state, indent, flatten)
            else:
                notFlat._render(state, indent, flatten)

        Doc._Cat(req, doc1, doc2):
            doc1._render(state, indent, flatten)
            doc2._render(state, indent, flatten)

        Doc._Nest(req, indent = extraIndent, doc):
            doc._render(state, indent + extraIndent, flatten)

        Doc._Group(req, doc):
            if not flatten:
                flatten = match req:
                    _SpaceReq.Infinite: Bool.True
                    _SpaceReq.Exact(req): state.column + req <= state.width
            doc._render(state, indent, flatten)

# Space requirement.
type _SpaceReq:
    Exact(U32)
    Infinite

impl ToStr[_SpaceReq]:
    toStr(self: _SpaceReq) Str:
        match self:
            _SpaceReq.Exact(req): "_SpaceReq.Exact(`req`)"
            _SpaceReq.Infinite: "_SpaceReq.Infinite"

impl Add[_SpaceReq]:
    __add(self: _SpaceReq, other: _SpaceReq) _SpaceReq:
        if self is _SpaceReq.Exact(req1) and other is _SpaceReq.Exact(req2):
            return _SpaceReq.Exact(req1 + req2)
        _SpaceReq.Infinite

Doc._req(self) _SpaceReq:
    match self:
        Doc._Empty: _SpaceReq.Exact(0)
        Doc._Str(lenChars, ..): _SpaceReq.Exact(lenChars)
        Doc._Blank(spaces): _SpaceReq.Exact(spaces)
        Doc._IfFlat(flat, ..): flat._req()
        Doc._HardLine: _SpaceReq.Infinite
        Doc._Cat(req, ..) | Doc._Nest(req, ..) | Doc._Group(req, ..): req

_countChars(s: Str) U32:
    let i = u32(0)
    for x: Char in s.chars():
        i += 1
    i

Doc.empty() Doc: Doc._Empty

Doc.str(str: Str) Doc: Doc._Str(str, lenChars = _countChars(str))

Doc.char(c: Char) Doc:
    # TODO: Implement a shorthand char to string
    let buf = StrBuf.withCapacity(1)
    buf.push(c)
    Doc.str(buf.toStr())

Doc.space() Doc: Doc._Str(str = " ", lenChars = 1)

Doc.hardLine() Doc: Doc._HardLine

Doc.blank(spaces: U32) Doc: Doc._Blank(spaces)

Doc.ifFlat(doc1: Doc, doc2: Doc) Doc:
    match doc1:
        Doc._IfFlat(flat = doc1, ..) | doc1:
            Doc._IfFlat(flat = doc1, notFlat = doc2)

Doc.whenFlat(doc: Doc) Doc:
    Doc.ifFlat(doc, Doc.empty())

Doc.whenNotFlat(doc: Doc) Doc:
    Doc.ifFlat(Doc.empty(), doc)

Doc.break_(i: U32) Doc:
    Doc.ifFlat(Doc.blank(i), Doc.hardLine())

Doc.nest(self, indent: U32) Doc:
    Doc._Nest(req = self._req(), indent, doc = self)

Doc.nested(indent: U32, doc: Doc) Doc:
    doc.nest(indent)

Doc.group(self) Doc:
    let req = self._req()
    if req is _SpaceReq.Infinite:
        self
    else:
        Doc._Group(req, doc = self)

Doc.cat(self, doc2: Doc) Doc:
    if self is Doc._Empty:
        return doc2

    if doc2 is Doc._Empty:
        return self

    Doc._Cat(req = self._req() + doc2._req(), doc1 = self, doc2)

impl Add[Doc]:
    __add(self: Doc, other: Doc) Doc: self.cat(other)
