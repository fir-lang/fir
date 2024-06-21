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

# Goals and non-goals

We want Fir to be your go-to programming language when you need types, with
modern tooling (compiler, language server, documentation generator, formatter,
build system, all in one executable), syntax, batteries-included approach to
the standard libraries, and an expressive type system.

# Current status and plans

Currently only a simple interpreter is available. The interpreter does not have
a type checker yet, it ignores all types.

The goal is to bootstrap the language as quickly as possible. To that end, we
only add features to the interpreter when the cost of implementing the feature
in the interpreter is paid off by writing the bootstrapping compiler with that
feature.

For example, implementing a type checker in the interpreter makes sense, as it
will be difficult to write the bootstrapping compiler without a type checker.

As an example feature that we probably don't want: the interepreter currently
doesn't have a garbage collector and it will probably not need a garbage
collector. The interpreter only needs to be able to run bootstrapping compiler
when compiling itself. 16 GB RAM (which I suspect most development PCs have
these days) should be enough for this.
