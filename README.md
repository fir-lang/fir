# Fir programming language

\[[Online interpreter]\]
\[[Examples]\]

[Online interpreter]: https://fir-lang.github.io
[Examples]: https://github.com/fir-lang/fir/tree/main/examples

Fir is a programming language that aims to bring high-level programming with
expressive types and typeclasses to the masses.

Some notable features are:

- Statically typed:
  - No runtime type checks or casts
  - Algebraic data types (ADTs) and pattern matching
  - Typeclasses (called traits)
  - Higher-kinded types
  - Anonymous polymorphic products (records) and sums (variants)

- Indentation sensitive syntax

- Compile-time monomorphisation.

  Runtime polymorphism is possible via trait objects. By default polymorphic
  code is monomorhised in compile time.

  This allows efficient memory layout in types like `Vec`: `Vec[I32]` holds a
  memory with 32-bit integers, instead of a memory with pointers to boxed
  32-bit integer objects.

  It also allows unboxing objects with immutable fields.

- Whole-program compilation

  Type checking and desugaring is done in a modular way.

  Any analyses for performance, and code generation, are done for the whole
  program.

  This allows simple implementation of monomorphisation, and simple and
  efficient implementation of runtime polymorphism (when using trait objects).

- Coroutines

## Goals

## Current status
