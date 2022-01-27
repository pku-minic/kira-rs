# Kira (Rust version)

Kira is an example compiler for PKU compiler course, it can compile SysY language into [Koopa IR](https://github.com/pku-minic/koopa) and RISC-V assembly.

`kira-rs` is written in Rust, for C++ example, please see [`kira-cpp`](https://github.com/pku-minic/kira-cpp).

## Usage

```sh
# compiler `input.c` to Koopa IR
cargo run -- -koopa input.c -o output.koopa
# compiler `input.c` to RISC-V assembly
cargo run -- -riscv input.c -o output.S
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## Copyright and License

Copyright (C) 2010-2022 MaxXing. License GPLv3.
