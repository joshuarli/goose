![The Goose programming language](docs/logo/logo_black_fg_white_bg_mini.png)

# The Goose Programming Language

Goose is a memory-safe systems language with no heap allocator or garbage
collector. Dynamic values live inline on compiler-managed data stacks, and
scope exit reclaims them.

[Tutorial](docs/tutorial.md) · [Reference](docs/reference.md) · [Language specification](docs/goose_spec.md) ·
[Standard library](docs/stdlib.md) · [Packages](docs/packages.md) ·
[Samples](samples/README.md) · [Benchmarks](bench/summary.md)

## What makes Goose different

- **Data stays in place.** Growing a grow-only array does not move its existing
  elements, so references into it remain valid.
- **Lifetimes are inferred.** The compiler checks that references do not outlive
  the data they point to. Goose needs no lifetime annotations.
- **Values are built inline.** Nested arrays and records need no per-object
  heap allocation. Generic functions are specialized at compile time.
- **C interop is direct.** Declare an `extern fn` for a C function. By default,
  Goose uses its `legacy` pipeline and emits one C translation unit for an
  ahead-of-time build.

## Install

A source build needs CMake 3.27 or later and a C++20 compiler. On macOS or Linux,
build and install with:

```sh
git clone https://github.com/aardappel/goose
cd goose
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --config Release
cmake --install build --prefix "$HOME/.local"
```

Add `~/.local/bin` to `PATH`. Choose an appropriate install prefix on Windows
and add its `bin` directory to `PATH`. The install includes `goose`,
`goose-lint`, and the standard-library sources.

The default build does not bundle the blessed `audio`, `gfx`, `physics`, or
`ui` packages. When a program imports one, Goose fetches and builds it on first
use. See the [package guide](docs/packages.md) for package setup, native
dependencies, and compiler selection.

## Run a program

```sh
goose run samples/01_tour.goose
goose check samples/01_tour.goose
goose build samples/01_tour.goose
```

`goose run` executes a program in the compiler process. `goose check` checks it
without running it. `goose build` creates an executable beside the source file;
use `-o` to choose another path. `goose build` needs a C compiler.

`goose toolchain` reports the selected C compiler. Choose one with `--cc`,
`GOOSE_CC`, or `cc = "clang";` in `~/.goose/config`. Run `goose` without a
source file to see command syntax.

## Documentation

- [Tutorial](docs/tutorial.md): learn Goose by example.
- [Language specification](docs/goose_spec.md): the complete language rules.
- [Standard library](docs/stdlib.md): 11 modules in `stdlib/`.
- [Packages](docs/packages.md): four blessed modules (`audio`, `gfx`,
  `physics`, `ui`) and external libraries.
- [Samples](samples/README.md): complete programs from a language tour to
  graphics and tools.
- [Benchmarks](bench/summary.md): benchmark results and methodology.

Goose is under active development. See the specification's
[open items](docs/goose_spec.md#appendix-b-todo-open-items) for known gaps.

## License

Goose is available under the [Apache License, Version 2.0](LICENSE).
