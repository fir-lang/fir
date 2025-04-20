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

  Runtime polymorphism is possible via trait objects. By default, polymorphic
  code is monomorphised at compile time.

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

For introduction, see blog posts:

- [Error handling in Fir][1]
- [Throwing iterators in Fir][2]

[1]: https://osa1.net/posts/2025-01-18-fir-error-handling.html
[2]: https://osa1.net/posts/2025-04-17-throwing-iterators-fir.html

# Goals

We want Fir to be a productive programming language when you need static types,
with modern tooling (compiler, language server, documentation generator,
formatter, build system, all in one executable), syntax, a batteries-included
approach to the standard libraries, and an expressive type system.

# Development plan

We want to bootstrap Fir as quickly as possible.

To that end, only features that will help writing the bootstrapping compiler
should be added to the interpreter, such as the type checker.

Features that are not absolutely needed to run the bootstrapping compiler will
be left to the bootstrapped compiler. For example, the interpreter does not
need to have a garbage collector.

Initially the compiler will only generate Wasm. In the long term we should have
native backends as well.
