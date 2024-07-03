# Fir programming language

\[[Online interpreter]\]
\[[Examples]\]

[Online interpreter]: https://fir-lang.github.io
[Examples]: https://github.com/fir-lang/fir/tree/main/examples

Fir is a programming language that aims to bring high-level programming with
expressive types and typeclasses to the masses.

Some notable features are:

- Statically typed:
  - Algebraic data types (ADTs) and pattern matching
  - Typeclasses (called traits)
  - Higher-kinded types
  - Anonymous polymorphic products (records) and sums (variants)

- Indentation sensitive syntax

- Compile-time monomorphisation

  Runtime polymorphism is possible via trait objects. By default polymorphic
  code is monomorhised in compile time.

  This allows efficient memory layout in types like `Vec`: `Vec[I32]` holds a
  memory with 32-bit integers, instead of a memory with pointers to boxed
  32-bit integer objects.

  It also allows unboxing objects with immutable fields (such as `Option`,
  `Result`), and multiple return values without allocation via records.

- Whole-program compilation

  Type checking and desugaring is done in a modular way.

  Any analyses for performance, and code generation, are done for the whole
  program.

  This allows simple implementation of monomorphisation, and simple and
  efficient implementation of runtime polymorphism (when using trait objects).

- Coroutines

- Tail call elimination (explicit with a keyword)

# Goals

We want Fir to a productive programming language when you need static types,
with modern tooling (compiler, language server, documentation generator,
formatter, build system, all in one executable), syntax, batteries-included
approach to the standard libraries, and an expressive type system.

# Current status

Currently only a simple interpreter is available. The interpreter does not have
a type checker yet, it ignores all types.

# Development plan

We want to bootstrap Fir as quickly as possible.

To that end, only features that will help writing the bootstrapping compiler
should be added to the interpreter, such as the type checker.

Features that are not absolutely needed to run the bootstrapping compiler will
be left to the bootstrapped compiler. For example, the interpreter does not
need to have a garbage collector.

Initially the compiler will only generate Wasm. In the long term we should have
native backends as well.

# Contributing

If the design and goals sound interesting, this is a great time to start
contributing to Fir.

Currently we only have a simple interpreter that runs some simple programs, so
the code is simple. If you are familiar with PL development than there should
be nothing new or different.

Some important tasks to be able to implement the bootstrapping compiler:

- Implement a type checker in the interpreter:
  [#7](https://github.com/fir-lang/fir/issues/7)

- Implement tests: [#8](https://github.com/fir-lang/fir/issues/8)

- Implement libraries needed for the bootstrapping compiler:
  [#9](https://github.com/fir-lang/fir/issues/8)
