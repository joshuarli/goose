# Repository conventions

## Goose source formatting

- Do not run `format_goose.py` on existing `.goose` source or test files. Preserve their current layout and keep edits limited to the changed behavior.
- Newly added `.goose` tests and reproducers may be formatted with `python scripts/format_goose.py <files>` and checked with `python scripts/format_goose.py --check <files>`.
- Keep deliberately malformed parser fixtures in `test/errors/` as written. Their source layout and diagnostics are part of the test.
- Use descriptive names and blank lines between distinct parts of a test. Formatting does not replace making the code understandable.
- Never include formatter-only changes in an upstream fix.

## Upstream pull requests

- Use titles such as `fix(parser): describe the behavior` or `fix(typecheck): describe the behavior` for fixes.
- Write descriptions with `## What`, `## Why`, `## How`, and `## Testing`, in that order. Keep each section short and concrete.
- Keep reproducer prose to the observed before/after result and one environment record. Add a `## Reproduction` section with the exact build/run commands in a `sh` block, followed by the minimal tested Dockerfile in a `dockerfile` block. Avoid repeating revisions, flags, setup instructions, or background already evident in the code.
- Describe the observable failure and resulting behavior before implementation details.
- Report checks actually run. Claim a regression fails before the fix and passes afterward only when that comparison has been verified.
- A fix for pathological input must also preserve performance on common input. Measure representative valid workloads and normal workloads that exercise the changed path against the exact base revision before recommending the change.
- Use identical compiler/build flags and inputs, warm up both versions, and alternate repeated measurements. Report timing, peak memory when allocation changes, sample counts, and variability; do not infer normal-case performance from a pathological regression alone.
- Include real before/after measurements, the commands and workload sizes, and their limits in the PR's Testing section. Surface regressions and explain any tradeoff; do not describe a change as performance-neutral without evidence.
- Before opening a draft PR, run its exact Docker reproducer locally and verify both the expected baseline failure and the fixed behavior. A draft is not an exception to verification. If the reproducer cannot run, report the blocker before opening the PR.
- Record the actual compiler name/version, musl or glibc version, architecture, and kernel from `uname`, together with build/runtime flags. Thread that environment through the test and performance results rather than implying that different environments are interchangeable.
- Use Clang 23 and the current stable GCC release for local upstream-fix verification, on a current Ubuntu or Debian image that packages them. GCC is currently 16.2.0; select `gcc-16` and `g++-16` explicitly, and update that version when a newer stable series ships. Record both compiler versions.
- Include a self-contained Dockerfile and exact build/run commands in the PR description only. Pin its base image by digest and source revisions, assert the expected failure and fixed result, and print the toolchain/libc/kernel used. Docker uses the host kernel, so the maintainer's kernel may differ from the recorded test kernel.
- Use shell for Docker reproducers. Do not add Python or a general benchmark harness when shell commands can demonstrate the failure and fix.
- Fetch pinned commit ZIP archives with Docker `ADD` and unpack them with CMake's archive command; do not install Git or another download tool just to obtain reproducer sources.
- Keep fork tooling out of upstream fix branches.
- Do not git push.

### Example PR description

The description for [PR #20](https://github.com/aardappel/goose/pull/20) demonstrates these conventions:

````markdown
## What

Accept reordered struct and enum initializers containing implicit references.

## Why

The safety check could read an untyped synthesized operand and crash.

## How

Inspect the operand type only for negation, where overflow-check ordering matters.

## Testing

Verified locally: baseline SIGSEGV (139); fix passes runtime assertions and matches expected stdout. Compiler: Clang/CMake Debug; generated C: `-O0 -DGS_DEBUG=1`.

Tested with `Debian clang version 23.1.3 (1)`, `ldd (Debian GLIBC 2.43-7) 2.43`. Docker host kernel (`uname -srvm`):

```text
Linux 6.18.33-0-lts #1-Alpine SMP PREEMPT_DYNAMIC 2026-05-24 18:06:34 x86_64
```

## Reproduction

```sh
docker build --progress=plain -t goose-pr20-repro .
docker run --rm goose-pr20-repro
```

```dockerfile
FROM debian:sid-slim@sha256:1f11c32b03195c1b28c55e4579755659edae5c76dd76a69b4e4fb34c58fa8744
RUN apt-get update && apt-get install -y --no-install-recommends clang-23 gcc-16 g++-16 cmake ninja-build && rm -rf /var/lib/apt/lists/*
WORKDIR /repro
ADD https://codeload.github.com/aardappel/goose/zip/de24a15659248fce28a1d5bdc8a6375bea322a0a base.zip
ADD https://codeload.github.com/aardappel/goose/zip/81004d20dc8f97b6e816bc7a20e1f2d4a07060f0 fix.zip
RUN for rev in base fix; do \
    cmake -E tar xf "$rev.zip" && mv goose-* "$rev" && rm "$rev.zip" || exit 1; done
RUN for rev in base fix; do \
    cmake -S "$rev" -B "$rev/build" -G Ninja -DCMAKE_BUILD_TYPE=Debug \
      -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23 \
      -DGOOSE_LIBTCC=OFF -DGOOSE_GFX=OFF -DGOOSE_AUDIO=OFF -DGOOSE_PHYSICS=OFF -DGOOSE_UI=OFF && \
    cmake --build "$rev/build" --parallel 2 || exit 1; done
RUN for rev in base fix; do \
    cmake -S "$rev" -B "$rev/build-gcc" -G Ninja -DCMAKE_BUILD_TYPE=Debug \
      -DCMAKE_C_COMPILER=gcc-16 -DCMAKE_CXX_COMPILER=g++-16 \
      -DGOOSE_LIBTCC=OFF -DGOOSE_GFX=OFF -DGOOSE_AUDIO=OFF -DGOOSE_PHYSICS=OFF -DGOOSE_UI=OFF && \
    cmake --build "$rev/build-gcc" --parallel 2 || exit 1; done
RUN cat > verify.sh <<'SH'
set -eu
ulimit -c 0
clang-23 --version | head -n 1
gcc-16 --version | head -n 1
ldd --version | head -n 1
uname -srvm
case_file=fix/test/codegen/reordered_implicit_reference_fields.goose
if base/build/goose --check "$case_file" > base.log 2>&1; then status=0; else status=$?; fi
[ "$status" -eq 139 ] || { cat base.log >&2; exit 1; }
fix/build/goose --standalone "$case_file" -o repro.c
clang-23 -O0 -DGS_DEBUG=1 repro.c -o program -lm -pthread
./program > actual.out
cmp actual.out fix/test/expected/reordered_implicit_reference_fields.out
if base/build-gcc/goose --check "$case_file" > base-gcc.log 2>&1; then status=0; else status=$?; fi
[ "$status" -eq 139 ] || { cat base-gcc.log >&2; exit 1; }
fix/build-gcc/goose --standalone "$case_file" -o repro-gcc.c
gcc-16 -O0 -DGS_DEBUG=1 repro-gcc.c -o program-gcc -lm -pthread
./program-gcc > actual-gcc.out
cmp actual-gcc.out fix/test/expected/reordered_implicit_reference_fields.out
echo 'PASS: baseline SIGSEGV reproduced; Clang and GCC fixed builds match expected output.'
SH
CMD ["sh", "verify.sh"]
```
````
