# This just tests parsing, but because parsed ASTs are printed after expanding
# macros, and macros are expanded after the whole program is parsed, we have to
# import actual modules here that the implementation can actually find and load.

import [
    Fir/Prelude,
    Fir/Prelude as P,
    Fir/Prelude/[min, max, Option, Result],
    Fir/Prelude/[
        min as _min,
        max as _max,
        Option as MyOption,
        Result as MyResult,
    ],
]


# args: --parse
