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

The [tutorial](docs/tutorial.md) walks through all of this by example, the
[reference](docs/reference.md) covers the whole language topic by topic,
the [specification](docs/goose_spec.md) has the exact rules, and the
[benchmarks](bench/results.md) have the numbers, losses included.

## Features

This section focuses on what distinguishes Goose. The [tutorial](docs/tutorial.md)
explains these features in more detail, and the [samples](samples/README.md)
show them in thirty-one complete programs.

### One memory model: stacks, and scope exit is the free

A program has the native call stack, static data and N data stacks, where the
compiler works out N. A data stack is a large address-space reservation with a
bump pointer, and there is no other memory. At most one resizable value is
live per stack and it is always on top, so growth never moves anything and
never checks a capacity. All of this is proved at compile time; the runtime
tracks only the bump pointers.

```goose
for round in 3 {
    var scratch: u8[>..] = [];                        // grow-only: growth is a pointer bump
    for i in 100000 { scratch.push((i % 256) as! u8); }
    print("round ", round, ": ", scratch.len, " bytes");
}                                                     // the free: one store to the stack top
```

### Nothing moves, so references survive growth

```goose
struct Item { id: i32, weight: f32 }

var items: Item[>..] = [];
let first .= items.push(Item { 1, 0.5 });             // a reference to element 0
for i: i32 in 2..1000001 { items.push(Item { i, 0.0 }); }
first.weight = 99.5;                                  // still valid, a million pushes later
```

`push` returns a reference to the new element, so a program can link elements
while building the array. A `vector<T>` or `Vec<T>` may reallocate and cannot
provide this guarantee. Stable references account for several benchmark gains.

### Safe references, no annotations

Every reference and slice has a static *root*: the variable that bounds its
target's lifetime. A reference must not outlive the variable that owns its
target or access that target through an incompatible type. The compiler infers
roots and specializes functions for them, so no annotations are needed. There
are no aliasing or exclusivity rules. When a lifetime check fails, the error
names the reference's root and its destination:

```goose
fn longest(a: u8[:], b: u8[:]) -> u8[:] { if a.len >= b.len { a } else { b } }

var outer: u8[>..] = [];
var w = outer[..];
{
    var inner: u8[>..] = [];
    format(inner, "inner text");
    w = longest(outer, inner);     // error: storing a reference rooted at inner,
}                                  //        which does not outlive the destination (§9.2)
```

A slice `T[:]` lets a function accept a range from any array kind without
copying its elements. For example, `split` returns slices into its input, and
a dictionary keyed by `u8[:]` stores views of strings rather than copies.

### Nested data stays inline

There is no single array type. There is a family that differs only in what
happens to the size, and every member is `[metadata][elements...]`, inline and
packed, never a pointer to an element block:

| Spelling | What it is |
|---|---|
| `T[k]` | fixed size, known at compile time |
| `T[]`, `T[varint]` | sized at construction, frozen after; a fixed or variable-width length |
| `T[..k]`, `T[..]` | capacity inline; grows and shrinks within it |
| `T[>..]` | **grow-only**: the workhorse; references into it stay valid |
| `T[>..<]` | **grow-shrink**: stacks, queues, heaps |

Strings are just `u8` arrays: `u8[>..]` is a builder, `u8[]` a finished string
stored inline in whatever holds it, `u8[..16]` a small string inside a struct,
`u8[:]` a view. A struct may contain variable-size parts, and they sit inline
in declaration order, so a record is a run of bytes with nothing indirect in it:

```goose
struct Item  { sku: u8[varint], qty: varint, cents: varint }
struct Order { id: varint, customer: u8[varint], items: Item[varint] }

var book: Order[>..] = [];
book.push(Order { id: 1001, customer: "alice",
                  items: [Item { sku: "SKU-441", qty: 2, cents: 1999 },
                          Item { sku: "SKU-7", qty: 1, cents: 500 }] });
```

That order is **29 bytes and 0 allocations**. As C++ `std::string` +
`std::vector<Item>` it is 160 bytes and 1 allocation, and as Rust `String` +
`Vec<Item>` 153 bytes and 4. A whole order book is one array that streams
through the cache. The price is that an array of variable-size elements is
sequential: you can iterate it but not index it (unless you keep a second
array of references into it as an index).

### Enums in two sizes

Algebraic data types are the only dynamic polymorphism: no inheritance, no
vtables. Every ADT can be stored two ways, chosen at the point of use. Fixed
mode (`Shape`) is a tag plus room for the largest payload, indexable and
overwritable. Variable mode (`Shape..`) gives each value exactly its variant's
size; the array becomes sequential and a value never changes variant, and in
exchange you may take references *into* a payload:

```goose
enum Shape { Circle { r: f64 }, Rect { w: f64, h: f64 }, Dot }

var packed: Shape..[>..] = [];                 // 9, 17 and 1 bytes, not 17 each
packed.push(Shape.Circle { r: 1.0 });
packed.push(Shape.Rect { w: 2.0, h: 3.0 });
packed.push(Shape.Dot);
for s in packed {
    match s { Rect &r => { r.w += 1.0; }, _ => {} }   // edits the payload in place, inside the array
}
```

*Case functions* provide another way to dispatch on a variant: define one
overload per variant. Calls dispatch on the tag through a jump table, and the
compiler checks that the overloads cover every variant:

```goose
fn area(s: Shape.Circle) -> f64 { 3.14159 * s.r * s.r }
fn area(s: Shape.Rect) -> f64   { s.w * s.h }
fn area(s: Shape.Dot) -> f64    { 0.0 }

for s in packed { print(s, " area ", area(s)); }
```

### Links narrower than pointers

A `T&` is a machine address: eight bytes, never dangling. A *relative reference*
is the same link stored as a narrow offset: `T&<u32>` is measured from the field
itself to a target in the same array, so the structure is position independent,
and `T&<u32 in pool>` from a named pool's base, so other arrays can link into
the pool. `T&<u32>?` uses offset 0 as null. Here is a binary search tree in one
grow-only array, with 12-byte nodes:

```goose
struct Node { key: i32, left: Node&<u32>?, right: Node&<u32>? }   // 12 bytes, links included

fn insert(pool: Node[>..]&, key: i32) {
    if pool.len == 0 { pool.push(Node { key: key }); return; }
    var cur .= pool[0];                             // .= binds a reference; = would copy the node
    loop {
        if key == cur.key { return; }
        let next = if key < cur.key { cur.left } else { cur.right };
        if next { cur .= next; continue; }          // narrowed by `if`: next is a Node&
        if key < cur.key { cur.left .= pool.push(Node { key: key }); }
        else             { cur.right .= pool.push(Node { key: key }); }
        return;
    }
}
```

References are transparent (no `*`, no `->`), `.=` binds or retargets one, and
`Node?` is a nullable reference that `if`, `guard` and `assert` narrow. The
insert is one push and one store, and the push cannot invalidate `cur`. When
lifetimes are not nested, a `reusable` pool pairs a grow-only array with a
hidden freelist: `alloc_ref` reuses a slot or pushes, `free` hands one back,
and since nothing is ever actually freed, a stale slot reads a *different value
of the correct type* rather than corrupting memory.

### Your data is already a file format

```goose
var image: u8[>..] = tree.to_bytes();           // a framed byte image of the whole array
var loaded, ok = from_bytes<Node[>..]>(image);  // verified before it becomes a value
image[image.len - 3] = 200;                     // tamper with a link ...
var bad, bok = from_bytes<Node[>..]>(image);    // ... and it is false and an empty array
```

The tree's links are self-relative, so it means the same thing wherever it
sits: saving is writing its bytes and loading is reading them back, with no
serializer, no schema and no pointer fixups. `from_bytes` checks the framing,
every tag, every length and every link before the bytes become a value, so a
corrupt or hostile file is a `false`, never a wild reference.

### Built in place, always

The copy-free construction guarantee
([spec §4.3](docs/goose_spec.md#43-the-in-place-construction-guarantee)) says a
constructed value is always built in its final home, propagated top-down
through calls. A function returning a grow-only array by value writes its
elements straight into the caller's variable, or into a field of the record
being built inside another array, so out-parameters mostly do not appear.

```goose
words.push(str("word", i));                    // formatted straight into the new element
let evens = xs.filter() { it % 2 == 0 };       // built straight into `evens`: no temporary
book.push(Order { id: 1001, customer: "alice", items: parse_items("SKU-441:2:1999;SKU-7:1:500") });
```

### Returning errors across calls

```goose
struct User { name: u8[..16], age: i32 }

fn load(text: u8[:]) -> User[>..], u8[] {
    var users: User[>..] = [];
    each_split(text, '\n') { users.push(parse_user(it)); };
    return users, "";
}

fn parse_user(line: u8[:]) -> User {              // returns a User: no Result, no error parameter
    let comma = find(line, ",");
    guard comma >= 0 else { return [], str("expected name,age: ", line) from load; }
    let age, ok = parse_int(line[comma + 1..]);
    guard ok else { return [], str("bad age: ", line) from load; }
    let name = trim(line[..comma]);
    return User { name: name, age: age as i32 };
}
```

`return E from f` returns `E` as the result of the innermost active call of
`f`, however many frames up, and every function in between keeps its plain
signature. It is checked statically, so every call of `parse_user` must lie
inside a `load` call and nothing is uncaught at runtime. It is a hidden
discriminant checked per frame rather than an unwinder, and the message is
built directly where `load`'s caller wants it. The parsers in the samples use
it for every syntax error.

### Generics and function blocks

```goose
fn twice(x) { x + x }                              // an untyped parameter is a generic one

fn each_pair<T, F>(xs: T[:]) {                     // F is a function value: a compile-time entity
    for i in 0..xs.len - 1 { F(xs[i], xs[i + 1]); }
}

fn first_gap(xs: i64[:]) -> i64 {
    each_pair(xs) { a, b => if b - a > 1 { return a; } };   // returns from first_gap, not each_pair
    return -1;
}

let evens = xs.filter() { it % 2 == 0 };
let total = fold(xs, 0) { acc, x => acc + x };
sort(xs) { a, b => a > b };
```

Everything is monomorphized. Type arguments are inferred from argument types;
parameters absent from those types can be supplied explicitly. Function values
are passed as generic parameters: every call is direct and inlinable, they
cannot escape, and there are no closure objects or function pointers, so a
higher-order function compiles to exactly the loop it looks like. A block may
`return` from its lexically enclosing function, and nested functions see the
enclosing function's locals.

### Threads that share nothing

```goose
thread_fn worker() {                                // a separate program with its own memory
    loop {
        let job = qget<Job>();                      // blocks on the typed queue for Job
        guard job.n >= 0 else { break; }            // -1 means stop
        qput(Result { n: job.n, digits: count_digits(job.n) });
    }
}

for i in n { ids.push(thread_spawn(worker)); }
```

There is no shared mutable memory. A `thread_fn` and everything it calls is
compiled as its own program with its own data stacks and its own copies of the
globals. Values cross through typed queues, one per type, and must be *flat*,
with no references at any depth. That is cheap because a flat Goose value is
contiguous: a job or a result carries real data, pixels included, and crossing
is a `memcpy`.

A failed check or `abort` in a worker started with `thread_spawn_contained`
ends only that worker. Its message goes to whoever waits for it, not to
stderr, so a supervisor can log it and start another:

```goose
var why: u8[>..] = [];
while !thread_wait(thread_spawn_contained(serve, attempt), why) {
    log(why);                                       // "assert failed (serve.goose:12)"
    why.clear();
    attempt++;
}
```

The first `thread_wait(id, msg)` for a worker takes the message; a caller
that doesn't ask for it loses it.

### Plain C in, plain C out

```goose
extern fn hypot(x: f64, y: f64) -> f64;             // straight from libm
extern fn crc32_bytes(s: const u8[:]) -> u32;       // a slice crosses as { data, len }
extern fn stats_of(xs: i32[:], out: Stats&);        // a struct filled through a pointer
```

An `extern fn` binds a Goose signature to a C symbol. The `math` and `os`
modules use this interface. Only types with supported C representations may
cross the boundary; unsupported signatures are rejected at the declaration.
The compiler emits one C file for the whole program. The bundled TinyCC
backend can compile and run that C inside the Goose compiler's process.

### Where the speed comes from

Much of the speed comes from the memory model: no heap allocation or
per-object teardown, contiguous data, narrow links, and enums sized for the
variant they contain. Every index is bounds-checked, and the compiler removes
checks it can prove unnecessary. An `assert` on a slice length often lets a
kernel eliminate its remaining checks and vectorize. `--bce-lines` reports
the checks that remain. `checkfree fn` rejects a kernel if any bounds check
survives; index types let graph edges retain validation done during construction.
Benchmark measurements use whole-process wall-clock time, including teardown.

| Geometric mean over 16 benchmarks | vs idiomatic C++ | vs hand-optimized C++ | vs best safe Rust |
|---|---:|---:|---:|
| speed, MSVC backend | 3.51x | 1.24x | 1.13x |
| speed, clang backend | 3.54x | 1.26x | 1.19x |
| peak memory | 1.95x less | 1.32x less | 1.25x less |

The [summary](bench/summary.md) explains the gains and losses;
[results.md](bench/results.md) has every measurement, and
[design.md](bench/design.md) explains what the suite tests.

### What it costs you

* You think about where data lives: who owns this, and how long does its scope
  last. Usually the answer is "the function that builds it", and that is free;
  when it is not, it is a `reusable` pool.
* Recursive functions cannot keep growable data across a recursive call;
  scratch ends before the call, and what outlives it is passed in as a pool.
* Arrays of variable-size elements iterate but do not index (short of an index
  of references kept beside them), a fixed-mode enum cannot be pointed into,
  and a variable-mode one cannot be overwritten. You choose per container.
* No escaping closures, no function pointers, no dynamic dispatch beyond ADT
  tags, and whole-program compilation only.
* A slot handed back to a `reusable` pool and still named reads whatever its
  next owner put there: a logic bug, never memory corruption.

[Tutorial §18](docs/tutorial.md#18-what-it-costs-you) is the full list.

## Install a release

Prebuilt compilers for Windows (x64), Linux (x64) and macOS (Apple silicon
and Intel) are on the [releases page](https://github.com/aardappel/goose/releases),
with the graphics, audio, ui and physics packages compiled in. Unpack one
anywhere and put its directory on PATH: the compiler finds the standard
library, TinyCC's runtime and the packages beside itself, and keeps what it
builds under `~/.goose` (`GOOSE_HOME`). The archive also holds these docs, the
samples and the VS Code extension.

Running a program in-process (`goose file.goose`) needs nothing else on
Windows. On Linux it needs the C library's headers (`libc6-dev`, or
`glibc-devel`); on macOS, the SDK of the Xcode command line tools
(`xcode-select --install`). `goose build` also needs a C compiler: Visual
Studio 2022 or later, or clang, on Windows; gcc or clang elsewhere. The Linux
compiler needs glibc 2.35 or later (Ubuntu 22.04, Debian 12), the macOS one
macOS 13.3 or later. macOS keeps a downloaded archive's files from running
until `xattr -dr com.apple.quarantine` is run on the unpacked directory.

## Build and run

You need CMake 3.27 or later, a C++20 compiler (MSVC, clang or gcc) and Python
3 for the test and sample runners. TinyCC, which the in-process backend is
built from, is part of the tree. The graphics, audio, ui and physics
modules are packages in repositories of their own
([goose_gfx](https://github.com/aardappel/goose_gfx) and
[goose_physics](https://github.com/aardappel/goose_physics);
`docs/design/packages.md`): `-DGOOSE_BUILTIN_LIBS=all` fetches them at the
pinned tags (git, at configure time) and compiles them into the compiler, so
their programs run with nothing else installed. Without it the compiler
builds alone, and a program importing one of them has it built into
`~/.goose` the first time, which needs git, cmake and a C compiler.

```bash
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
```bash
build/goose build samples/01_tour.goose && samples/01_tour
build/goose build samples/27_gfx_cube.goose && samples/27_gfx_cube
```

`--debug` turns on the overflow, range and tag checks in the generated C, each
abort naming its source line (and an overflow or a cast the values involved),
and builds the C with debug information; `--dry-run` prints the commands a
build would run, for a build system of your own; `-v` prints them as they
run. Intermediates go under `~/.goose` (`GOOSE_HOME`), the runtime object
compiled once per C compiler. Useful flags of both forms: `-O0`/`-O1`/`-O2`
set the inlining level (a build defaults to `-O2`, a run to `-O1`),
`--bce-lines` reports the bounds checks kept per line, and `-DGS_DEBUG=1` is
what `--debug` defines. Every resizable value lives on a data stack of 2 GB
of reserved address space, committed as it is used: `--stack-reserve 16G`
changes that for a program, `--stacks` reports how many data stacks the
program and each of its workers can take and the cap that puts on
`hardware_threads()`, and `-DGS_STACK_STATS=1` makes a program report its
actual use as it ends.

A program with C of its own names it in a sidecar beside the source,
`foo.build` beside `foo.goose`: `c_sources = ["impl.c"];`, with `c_include`,
`c_defines`, `c_libs` and `_windows`, `_linux` or `_macos` variants of each
for one platform's part. Both forms build it: `goose build` links it in,
and `goose run` builds it into a library the in-process run loads, so an
`extern fn` reaches it either way. A library does the same with a sidecar
beside its entry (or names the static library target of its own CMake
project, `cmake_target = "x";`, which the compiler builds through cmake), and
a program takes a library with `import name from
"source";` in its root file: a directory (`"./lib"`), or a git repository
at a tag or commit (`"owner/repo@v1"` on GitHub, `"host/owner/repo@ref"`),
fetched into `~/.goose` and built there once per C compiler
(`docs/design/packages.md`).

Underneath, `goose -o tour.c tour.goose` writes the C, which holds the
program and the part of the runtime that inlines into it; the rest of the
runtime (the OS layer, data stack reservation, threads, printing) is one more
C file, which `goose --emit-runtime goose_runtime.c` writes, to be compiled
once and linked with every program (`cc -O2 tour.c goose_runtime.o -o tour
-lm -pthread`; on Windows `cl /O2 tour.c goose_runtime.obj`). Build the
runtime with the compiler and flags the programs use; it takes no `-D` of its
own, and a program from another version of the compiler fails to link
against it. `--standalone` writes a C file that holds the whole runtime
instead, and builds on its own. A program using `audio`, `gfx`, `physics` or
`ui` also links that module's layer, which `goose --audio-link msvc|cc`,
`--gfx-link`, `--physics-link` and `--ui-link` name in a response file (`cc
cube.c goose_runtime.o -o cube @$(goose --gfx-link cc)`, a ui program's
before the gfx one it draws through). `goose build --dry-run` prints all of
this for the program at hand.

A program using `audio` plays procedural mono/stereo PCM through SDL3 without
opening a graphics window. See the [audio reference](docs/stdlib.md#audio).

The test suite and the samples run on Windows, macOS and Linux:

```bash
python test/run_tests.py
python samples/run_samples.py
```

For editing, the [VS Code extension](vscode/README.md) gives syntax
highlighting, the compiler's language server (`goose lsp`: errors as you
type, hover, go to definition, completion, rename, symbols) and one-key runs
through the JIT:

```bash
code --install-extension vscode/goose-language.vsix
```

Other editors can run `goose lsp` themselves; [editors](docs/editors.md)
has the configuration for Neovim, Helix and Emacs.

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
