# Compiler correctness generation

This directory contains a bounded differential correctness check for Goose. Goose and the
language whose design informed this harness are greenfield projects with no users or deployed
programs. This work is for finding compiler mistakes during language development. It is not a
software-security project, and neither the generated programs nor the process runner form a
security boundary.

The harness generates terminating programs from typed representations, evaluates each
representation with a small independent model, compiles it through Goose and a native C
compiler, and compares the program's exact stdout with the model. Successful programs must write
nothing to stderr. The full matrix varies both optimizers independently:

| Goose | C |
| --- | --- |
| `-O0` | `-O0` |
| `-O0` | `-O2` |
| `-O2` | `-O0` |
| `-O2` | `-O2` |

Each lane has a strict recipe schema, renderer, independent evaluator and structural reducer:

| Lane | Modeled behavior |
| --- | --- |
| `aggregate` | Elementwise integer arithmetic over fixed arrays and nested packed structs, including compound and scalar forms. |
| `scalar` | Signed 64-bit integers, booleans, locals, assignments, branches, bounded loops, comparisons, short circuits and a pure helper call. |
| `numeric` | Every signed and unsigned integer width, defined wrapping, Euclidean remainder, masked shifts, comparisons and unchecked casts. |
| `order` | Left-to-right evaluation through effectful operands, destinations, fixed arrays, indices and slices. |
| `resize` | Small resizable integer arrays, including push, pop, `pop_n`, resize, append, clear, indexing and slicing. |
| `trap` | Required runtime checks for division, bounds, resize, pop, capacity and effect ordering. |

Validation proves arithmetic and access preconditions before the model or Goose runs. Recipes can
express `MustCompileAndReturn` or `MustTrap`; required rejections belong to a later family.

## Running it

Build a normal Goose compiler first. The optional native modules are not needed:

```sh
cmake -S . -B build/fuzzygoose -G Ninja -DCMAKE_BUILD_TYPE=Debug \
  -DGOOSE_LIBTCC=OFF -DGOOSE_GFX=OFF -DGOOSE_AUDIO=OFF \
  -DGOOSE_PHYSICS=OFF -DGOOSE_UI=OFF
cmake --build build/fuzzygoose --target goose
python3 fuzz/driver.py doctor --exe build/fuzzygoose/goose --cc clang
python3 fuzz/driver.py smoke --exe build/fuzzygoose/goose --cc clang
python3 fuzz/driver.py run --lane order --exe build/fuzzygoose/goose --cc clang \
  --duration 300 --count 10000
```

`doctor` runs one case at `-O0/-O0`. `smoke` defaults to eight cases at matching `-O0` and
`-O2`. `run` uses the full matrix and stops at the first finding. `--seed` makes the generated
sequence repeatable; without it, the selected seed is printed and stored. `--count`, `--duration`,
`--timeout`, and `--output-limit` bound a campaign. The current process cleanup implementation is
Linux-only. A case that starts before the campaign duration expires receives its full per-process
timeout; the duration prevents another case from starting after the deadline.

`--sanitize` instruments the generated C and its embedded runtime with ASan and UBSan. To check the
C++ compiler itself, pass a separately built sanitizer-instrumented Goose binary. Generated packed
C disables UBSan's alignment check, matching the repository's existing sanitizer profile; other
checks remain fatal.

## Clang and glibc container

The container profile builds Goose and both native compiler targets with Clang on Ubuntu's glibc.
The image contains every semantic lane, the source, and the compiler; only a named artifact volume
is writable during a read-only, network-disabled run:

```sh
docker build -f fuzz/docker/Dockerfile -t fuzzygoose-clang-glibc .
docker volume create fuzzygoose-work
docker run --rm --network none --read-only \
  --tmpfs /tmp:rw,nosuid,nodev,size=1g \
  --mount source=fuzzygoose-work,target=/work \
  fuzzygoose-clang-glibc
```

Override the image command for a longer lane:

```sh
docker run --rm --network none --read-only \
  --tmpfs /tmp:rw,nosuid,nodev,size=1g \
  --mount source=fuzzygoose-work,target=/work \
  fuzzygoose-clang-glibc \
  python3 fuzz/driver.py run --lane numeric \
    --exe build/fuzz-clang-glibc/goose --cc clang \
    --duration 300 --count 10000 --output /work/fuzz
```

The generated Goose subset has no filesystem, networking, subprocess or FFI operations. It cannot
name host files because the commands mount no host directory. Compiler-only mutation targets do
not execute their source inputs.

## Native compiler targets

`GOOSE_FUZZ=ON` adds Clang libFuzzer targets for parser dump/reparse stability and the complete
parse, resolve, typecheck, optimize, bounds-check and code-generation pipeline. Imports and
file-named shader inputs are rejected so the targets remain hermetic. For example, inside the
container:

```sh
mkdir -p /work/parser-corpus
cp test/syntax/*.goose /work/parser-corpus/
build/fuzz-clang-glibc/goose_fuzz_parser /work/parser-corpus \
  -max_total_time=300 -timeout=10 -artifact_prefix=/work/parser-
```

Each campaign gets a unique directory under `build/fuzz/`. A finding contains its source, strict
recipe, seed and oracle result, raw base64-encoded process output, generated C, exact commands,
tool identities, repository state, and a replay command. Replay or structurally reduce it with:

```sh
python3 fuzz/driver.py replay build/fuzz/run-.../failure-... \
  --exe build/fuzzygoose/goose --cc clang
python3 fuzz/driver.py reduce build/fuzz/run-.../failure-... \
  --exe build/fuzzygoose/goose --cc clang --reduction-seconds 60
```

Reduction keeps the same failure class, stage, and optimizer configuration and recomputes the
independent result after each candidate. The original artifact is copied before reduction begins.

Run the harness self-tests with:

```sh
python3 -m unittest discover -s fuzz -p 'test_*.py' -v
```

They cover deterministic generation and recipe validation, model semantics, structured reduction,
failure classification, exact output comparison, artifact preservation, output limits, timeouts,
signal reporting, and descendant cleanup. The tests inject compiler rejection, crashes, C build
failure, traps, output mismatch, and sanitizer diagnostics without adding fault switches to Goose.

## Limits and guarantees

The driver clears the subprocess environment, uses a temporary working directory, closes stdin,
bounds captured output and elapsed time, and kills and reaps the Linux process group. These are
repeatability and cleanup measures. They do not make compilation or execution safe for hostile
input. The execution lane accepts only programs rendered from the closed typed representation; it
does not execute mutated source, FFI, file access, networking, subprocesses, or user-provided code.

The harness does not yet provide required-rejection oracles, storage/lifetime families,
serialization-byte fuzzing, source coverage, parallel semantic
workers, or non-Linux process cleanup. It is development evidence over bounded generated subsets,
not evidence that Goose is sound.
