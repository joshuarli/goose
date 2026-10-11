# Performance evidence

These measurements compare the starting revision `e023e99cde39e9ad619f05f4731c03a9ed90ed2c` with the linter working tree. Both compiler builds used CMake Debug, GCC 15.2.0, `-g -std=gnu++20 -Wall -Wextra -Wno-missing-field-initializers`, and `GOOSE_BUILTIN_LIBS=`. Inputs, flags, working directory, and `GOOSE_STDLIB` were held constant. The host was Alpine Linux with musl, x86_64, kernel `Linux 7.2.9-2-stable #3-Alpine SMP PREEMPT_DYNAMIC 2026-10-06 20:49:35 x86_64`; CMake was 4.3.4.

## Ordinary compiler checks

Each build was warmed once, then base and linter-tree runs alternated. Shapes,
records, and the high-specialization program used 21 samples; the multi-module
and Mini Doom programs used seven. The table reports median wall time, MAD,
and median change:

| Workload | Samples | Base `--check` | Linter-tree `--check` | Median change |
|---|---:|---:|---:|---:|
| `samples/05_shapes.goose` | 21 | 5.780 ms (MAD 0.238 ms) | 5.732 ms (MAD 0.163 ms) | −0.84% |
| `samples/16_records.goose` | 21 | 73.215 ms (MAD 1.735 ms) | 72.299 ms (MAD 1.887 ms) | −1.25% |
| `test/goose_in_goose/main.goose` | 7 | 1.240 s (MAD 41.8 ms) | 1.199 s (MAD 3.3 ms) | −3.31% |
| `samples/31_mini_doom.goose` | 7 | 197.504 ms (MAD 3.306 ms) | 197.635 ms (MAD 4.293 ms) | +0.07% |
| `tools/lint/main.goose` | 21 | 833.920 ms (MAD 60.270 ms) | 799.034 ms (MAD 50.557 ms) | −4.18% |

These runs show no persuasive regression over the campaign's approximate 5%
ordinary-check threshold. The two 21-sample cases have wide absolute timing
variation but close medians.

The timed commands were `goose --check --stdlib /home/josh/d/goose/stdlib
<source>` and `goose lint <source> --stdlib /home/josh/d/goose/stdlib --format
jsonl`; successful output was redirected to `/dev/null`. Both builds used
`cmake -S . -B <build> -DCMAKE_BUILD_TYPE=Debug -DGOOSE_BUILTIN_LIBS=`.

## Lint-only cost

Nine alternating measurements on the current build compared normal `--check`
with full `lint --format jsonl`. The staged runs timed facts production with a
minimal companion and the Goose rule engine with a captured facts file. Stage
timings include separate process starts and file I/O; their medians do not sum
exactly to the independently measured total.

| Workload | Facts | `--check` median (MAD) | Facts production median (MAD) | Goose engine median (MAD) | Full lint median (MAD) |
|---|---:|---:|---:|---:|---:|
| `samples/16_records.goose` | 461,260 B | 72.199 (1.030) ms | 172.474 (2.987) ms | 7.001 (0.259) ms | 160.783 (2.387) ms |
| `tools/lint/main.goose` | 2,158,939 B | 885.168 (49.096) ms | 1,292.499 (106.631) ms | 29.563 (0.878) ms | 1,268.119 (74.872) ms |

Fact production is the dominant added cost; the policy engine is small. Full
lint took about 2.2× the normal check time on the record sample and 1.4× on the
high-specialization compiler source. This exceeds the campaign's 20% lint
overhead investigation threshold. The exporter recomputed normalized source
paths inside sorting and record loops; memoizing one path per source reduced
the observed facts-production time. The remaining frontend/fact-export cost is
a measured tradeoff, not a claim of negligible overhead.

## Peak memory

Peak RSS (`wait4` `ru_maxrss`) from the seven-sample lint workload pass and the
corresponding base/current ordinary-check samples, in KiB, was:

| Workload | Base check | Linter-tree check | Full lint |
|---|---:|---:|---:|
| Shapes | 10,424 | 10,424 | 10,148 |
| Records | 14,096 | 14,760 | 15,768 |
| Multi-module compiler | 52,124 | 52,620 | 57,044 |
| Mini Doom | 21,068 | 21,964 | 24,620 |
| High-specialization linter source | 30,140 | 30,872 | 36,964 |

Lint stayed below 1.5× the corresponding normal-check peak RSS in these
workloads. The multi-module run measured `test/goose_in_goose/main.goose`; the
high-specialization workload was the linter's own source (356 checked
specializations). Measurements are host-specific and do not replace the
Linux, macOS, and Windows CI matrix.
