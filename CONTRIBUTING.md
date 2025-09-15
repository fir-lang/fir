# Contributing to Fir

## Setup

Development requires a stable version of [Rust](https://www.rust-lang.org/). 

You will also need a global installation of libraries [Just](https://github.com/casey/just), [LALRPOP](https://github.com/lalrpop/lalrpop), and [Golden Tests](https://github.com/jfecher/golden-tests). Installation instructions for Just is provided in its documentation. Install LALRPOP with `cargo install lalrpop`. The Golden Tests library is used as a binary in our `justfile` and can be installed to support this with the following command:

```
cargo install goldentests --features binary
```

Use the `just test` command to run the tests.
