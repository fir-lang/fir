prim type I32

prim type Str

type A:
    A

trait Test[A]:
    type T
    fn test(self): T

impl Test[A]:
    type T = I32
    fn test(self): Str =
        "hi"

# args: --typecheck --no-prelude --no-backtrace
# expected stderr:
# tests/AssocTysFail2.fir:14:5: Trait method implementation of test does not match the trait method type
#                                 Trait method type:          Scheme { quantified_vars: [], ty: Fun([Con("A")], Con("T")), loc: Loc { module: "tests/AssocTysFail2.fir", line_start: 9, col_start: 4, byte_offset_start: 75, line_end: 9, col_end: 19, byte_offset_end: 90 } }
#                                 Implementation method type: Scheme { quantified_vars: [], ty: Fun([Con("A")], Con("Str")), loc: Loc { module: "tests/AssocTysFail2.fir", line_start: 13, col_start: 4, byte_offset_start: 128, line_end: 14, col_end: 12, byte_offset_end: 161 } }
