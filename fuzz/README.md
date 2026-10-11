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
| `parse_flt` | Standard-library decimal parsing, with an independent host conversion and generated leading-zero, fraction, exponent and invalid-input cases. |
| `reference` | Mutable/read-only references into locals, fixed arrays and structs, rebinding, recursive aliases, slices and required lifetime rejections. |
| `resize` | Small resizable integer arrays, including push, pop, `pop_n`, resize, append, clear, indexing and slicing. |
| `serialize` | Valid and hostile byte images with self-relative links, fixed ADTs, limited arrays and variable fields; independent validation and canonical round trips. |
| `trap` | Required runtime checks for division, bounds, resize, pop, capacity and effect ordering. |

Validation proves arithmetic and access preconditions before the model or Goose runs. Recipes can
express `MustCompileAndReturn`, `MustTrap`, or `MustReject`. A required rejection succeeds only when
Goose exits cleanly with the modeled diagnostic category; acceptance, a crash, a sanitizer report,
or an unrelated diagnostic is a finding.

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

The driver emits C once for each Goose optimization level, then compiles that C at every requested
C optimization level. The full matrix therefore uses two Goose invocations and four C/program
invocations per returned case. Report rows represent actual invocations, so a Goose-stage row has
`c_opt: null`; C and program rows retain their concrete C level. Rejection recipes stop after each
Goose level.

`--sanitize` instruments the generated C and its embedded runtime with ASan and UBSan. To check the
C++ compiler itself, pass a separately built sanitizer-instrumented Goose binary. Generated packed
C disables UBSan's alignment check, matching the repository's existing sanitizer profile; other
checks remain fatal. Leak checking is disabled for generated programs because LeakSanitizer
requires ptrace access on some hosts.

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
file-named shader inputs are rejected so the targets remain hermetic.

The pipeline target compiles every input at `-O0`, `-O1`, and `-O2`, requires consistent
acceptance, perturbs compiler state, and repeats every level. Generated C is compared only between
repeat compilations at the same level. Semantic equivalence across levels remains the job of the
modeled execution lanes.

The checked-in pipeline corpus includes reference aliasing, serialization, variable ADTs and the
smaller syntax/control-flow seeds. `fuzz/native/goose.dict` supplies Goose declarations, types,
references, array forms and serialization tokens. Run isolated, measured campaigns with:

```sh
python3 fuzz/native_campaign.py --target pipeline \
  --exe build/fuzz-clang-glibc/goose_fuzz_pipeline \
  --duration 300 --seed 12345 --output /work/fuzz
python3 fuzz/native_campaign.py --target parser \
  --exe build/fuzz-clang-glibc/goose_fuzz_parser \
  --duration 300 --seed 12345 --output /work/fuzz
```

Each summary records edge and feature coverage, corpus growth, throughput, peak memory and failure
artifact hashes. Pipeline summaries also report valid-source acceptance and the furthest compiler
stage reached. These values make short probe runs comparable before assigning a longer budget.

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

## Historical calibration

Seeds zero in `parse_flt`, `serialize`, and `reference` are pinned calibration cases for PRs
#21, #22 and #23. Their common buggy revision is
`de24a15659248fce28a1d5bdc8a6375bea322a0a`; the fixed revisions are stored in
`fuzz/calibrate.py`. Given compiler builds from those revisions, verify a pair with:

```sh
python3 fuzz/calibrate.py pr21 --buggy-exe /path/to/base/goose \
  --fixed-exe /path/to/pr21/goose --cc clang-23
python3 fuzz/calibrate.py pr22 --buggy-exe /path/to/base/goose \
  --fixed-exe /path/to/pr22/goose --cc clang-23
python3 fuzz/calibrate.py pr23 --buggy-exe /path/to/base/goose \
  --fixed-exe /path/to/pr23/goose --cc clang-23
```

Calibration succeeds only when the buggy compiler produces the expected failure class and stage
and the fixed compiler passes the same full matrix. PR #22 additionally requires sanitizer
instrumentation.

## Limits and guarantees

The driver clears the subprocess environment, uses a temporary working directory, closes stdin,
bounds captured output and elapsed time, and kills and reaps the Linux process group. These are
repeatability and cleanup measures. They do not make compilation or execution safe for hostile
input. The execution lane accepts only programs rendered from the closed typed representation; it
does not execute mutated source, FFI, file access, networking, subprocesses, or user-provided code.

The reference model currently covers scalar and one-element slice locations in locals, fixed
arrays and flat structs; it does not yet model nested variable-size holders or self-relative
reference construction. The serialized image model covers optional self-relative links at every
fixed offset width, fixed ADT tags, limited fields and variable byte fields. Nested combinations,
variable-mode ADTs and varint relative links remain future extensions. The harness does not
provide parallel semantic workers or non-Linux process cleanup. It is development evidence over
bounded generated subsets, not evidence that Goose is sound.
