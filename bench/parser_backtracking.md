# Generic-argument backtracking measurements

Status: rejected. The patch was reverted from the local integration branch.

The published patch has a measurable cost on valid comparison-heavy code:
+11.64% with GCC/musl and +39.76% with Clang/glibc. It greatly improves the
malformed nested ambiguity case. Revise the ordinary comparison path before
recommending the patch as performance-neutral; the pathological improvement
alone does not establish that common cases remain fast.

The added rollback loops visit only allocations from failed speculation, and
those objects otherwise survive until AST teardown. These measurements cover
the cleanup and failure cache together; they do not isolate their individual
costs. Caching unique ordinary comparison positions cannot provide a repeat
parse benefit for those positions.

## Revisions and workloads

- Exact base: `de24a15659248fce28a1d5bdc8a6375bea322a0a`.
- Published head: `b37cebb737200510e18839eb9db2da5e49896279`.
- Comparisons: 50,000 valid `left < right` sites, in functions of 200 statements.
- Generics: 50,000 valid `identity<i64>(left)` sites, in functions of 200 statements.
- Each generated file is parsed/resolved 20 times per invocation: 1,000,000 sites.
- Corpus: twelve existing sample/benchmark programs, each repeated 80 times per
  invocation. Exact paths and source hashes are in the raw results.
- Pathological: the published 20-ambiguity error fixture, once per invocation.
- Nine measured base/head pairs after two warmup pairs, alternating which
  version runs first. Each invocation is pinned to one CPU. GNU time records
  process peak RSS; wall time includes startup, parsing, resolution and teardown.
- Generated valid workloads also pass `--check` on both versions.

## Tested environments

GCC/musl: `c++ (Alpine 15.2.0) 15.2.0`, musl 1.2.5, x86_64 Alpine 3.23.4;
compiler flags `-std=c++20 -O2 -DNDEBUG -pthread`; CPU affinity 4.

Clang/glibc: `Ubuntu clang version 18.1.3 (1ubuntu1)`,
`ldd (Ubuntu GLIBC 2.39-0ubuntu8.9) 2.39`, x86_64 Ubuntu 24.04 container;
CMake Release with both C/C++ release flags `-O2 -DNDEBUG`, C++20; CPU affinity 0.
The Clang container builds and links its own shader compiler library.
Optional native modules and TinyCC are disabled in both builds.

Both ran on AMD Ryzen 9 9950X with kernel:

```text
Linux 6.18.33-0-lts #1-Alpine SMP PREEMPT_DYNAMIC 2026-05-24 18:06:34 x86_64
```

The container base is pinned to:
`ubuntu:24.04@sha256:534baea6a22c03a63003dbc8dbe78fe34bc0d7e595d9a9dc9834884ff530eb55`.
Docker uses its host kernel; the image digest does not pin the kernel.

## Results

Positive changes mean slower parsing. RSS is median peak resident memory.

| Environment | Workload | Base median ms | Head median ms | Time change | Base / head RSS MiB | Base / head timing range ms |
|---|---|---:|---:|---:|---:|---|
| GCC/musl (host) | comparisons | 812.53 | 907.09 | +11.64% | 39.54 / 38.47 | 788.51–853.48 / 880.78–932.22 |
| GCC/musl (host) | generics | 875.32 | 878.46 | +0.36% | 51.29 / 51.30 | 862.90–897.77 / 866.16–909.16 |
| GCC/musl (host) | corpus | 752.28 | 770.98 | +2.49% | 6.89 / 6.91 | 722.96–783.52 / 734.89–813.96 |
| GCC/musl (host) | pathological | 4476.24 | 4.15 | -99.91% | 436.75 / 5.42 | 3775.00–4988.88 / 2.40–8.43 |
| Clang/glibc (Docker) | comparisons | 440.76 | 616.01 | +39.76% | 38.62 / 37.23 | 435.13–456.86 / 599.70–622.83 |
| Clang/glibc (Docker) | generics | 501.04 | 505.28 | +0.85% | 48.18 / 48.21 | 489.57–581.74 / 496.47–589.81 |
| Clang/glibc (Docker) | corpus | 500.81 | 513.73 | +2.58% | 5.79 / 5.88 | 488.99–552.28 / 494.93–549.83 |
| Clang/glibc (Docker) | pathological | 2810.14 | 3.22 | -99.89% | 418.72 / 5.20 | 2718.81–2819.71 / 2.73–5.91 |

Generic and corpus timing ranges overlap. Their small median differences do not
establish neutrality or a statistically significant regression. Comparison
ranges are separated in both environments. These are compiler front-end
measurements, not generated-program runtime or end-to-end codegen benchmarks.
The generated workloads exercise a common path at a large scale; they are not
a substitute for the real-program corpus. Toolchain, libc and pinned CPU differ
between environments, so the cross-environment difference is not attributable
to the compiler alone. The system is shared and CPU frequency is not locked.

The container additionally verifies a 24-ambiguity malformed input under a
one-CPU-second budget: the baseline terminates with SIGXCPU and the head returns
the expected indexing diagnostic. Both expected outcomes are asserted.

## Repeating the host measurement

Build both revisions with the identical flags above. Then run:

```bash
python bench/parser_backtracking.py \
  --base-exe /tmp/goose-pr19-base-opt \
  --head-exe /tmp/goose-pr19-head-opt \
  --source-root /tmp/goose-pr19-base \
  --output-dir build/pr19-performance-final \
  --base-revision de24a15659248fce28a1d5bdc8a6375bea322a0a \
  --head-revision b37cebb737200510e18839eb9db2da5e49896279 \
  --build-flags '-std=c++20 -O2 -DNDEBUG -pthread' \
  --compiler c++ --cpu 4 --repeats 20
```

The self-contained Dockerfile and its exact build/run commands are in the
upstream PR description. That Dockerfile was built and run locally; it fetches
pinned public source revisions and requires no mounted source tree.

Raw samples: [GCC/musl](parser_backtracking_results.json) and
[Clang/glibc](parser_backtracking_clang_glibc_results.json).
