# Changelog

All notable changes to the `kira-rs` will be documented in this file.

## Unreleased

### Changed

* Bumped dependency `koopa` to version 0.0.11.
* Bumped dependency `lalrpop` to version 0.23.2.
* Bumped dependency `regex` to version 1.13.2.

### Fixed

* Compiler panic when evaluating constant division or remainder by zero, or signed overflow cases like `(-2147483647 - 1) / -1`. These expressions now report a constant evaluation error.
* Logical `&&` and `||` did not short-circuit in constant expressions, so valid expressions like `0 && (1 / 0)` were rejected.
* Constant expressions now report undefined names and invalid operand types even in short-circuited operands.
* Function parameters were incorrectly rejected as duplicated definitions when their names matched a library function or a previously defined function.

## 0.0.6 - 2026-03-19

### Added

* [PR #1](https://github.com/pku-minic/kira-rs/pull/1): feat: support sourcemap of single file, optimize error message.

### Changed

* Bumped dependency `koopa` to version 0.0.10.
* Bumped dependency `lalrpop` to version 0.23.1.

## 0.0.5 - 2025-10-23

### Changed

* Bumped dependency `koopa` to version 0.0.8.
* Bumped dependency `lalrpop` to version 0.22.2.
* Bumped dependency `regex` to version 1.12.2.
* Bumped to Rust 2024 edition.

## 0.0.4 - 2023-06-02

### Changed

* Bumped dependency `koopa` to version 0.0.7.
* Bumped dependency `lalrpop` to version 0.20.0.

## 0.0.3 - 2023-01-12

### Changed

* Bumped dependency `regex` to version 1.5.6.
* Bumped dependency `koopa` to version 0.0.6.

### Fixed

* Some deprecated and non-recommended uses in the source code.

## 0.0.2 - 2022-02-17

### Changed

* Changed the constant type of evaluator from `i64` to `i32`.

### Fixed

* Problems about function parameters.
* Problems about array pointers.
* Problems about values in stack frame.

## 0.0.1 - 2022-01-27
