prim type Str
prim type I32

trait T[A]:
    fn toStr(self): Str

impl T[Str]:
    fn toStr(self): I32 =
        123

# args: --typecheck --no-prelude --no-backtrace
# expected stderr:
# tests/TcFail1.fir:8:5: Trait method implementation of toStr does not match the trait method type
#                                 Trait method type:          Scheme { quantified_vars: [], ty: Fun([Con("Str")], Con("Str")), loc: Loc { module: "tests/TcFail1.fir", line_start: 4, col_start: 4, byte_offset_start: 45, line_end: 4, col_end: 20, byte_offset_end: 61 } }
#                                 Implementation method type: Scheme { quantified_vars: [], ty: Fun([Con("Str")], Con("I32")), loc: Loc { module: "tests/TcFail1.fir", line_start: 7, col_start: 4, byte_offset_start: 83, line_end: 8, col_end: 11, byte_offset_end: 116 } }
