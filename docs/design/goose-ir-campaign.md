# Campaign: Lean-backed Goose semantics, Goose IR, and build scalability

**Status:** ready to execute. Nothing below is implemented.
**Branch:** `goose-ir`. **Base:** `62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a`. `master` is not touched.
**Contracts:** the [specification](goose-ir-spec.md) says what is built; the [validation plan](goose-ir-validation.md) says how each claim is proved. This document says in what order, by whom, and when it is done.

**Goal.** Two outcomes, pursued together. First, an executable, mechanically checked semantics for a Goose fragment and an opt-in IR pipeline that must agree with it. Second, a measurably shorter edit-build-verify loop for large programs: attribution of where build cost comes from, fewer emitted bodies with no weaker checking, and reuse of unchanged native code. A better-structured compiler that still regenerates and recompiles the whole program after a small edit does not meet the goal.

**Deliverables.**

1. Lean Typed Goose Core for `core-pilot`, `core-shrink` and `core-construction`: interpreter, validator, decoder, and the `goose-semantics` tool.
2. The Tier A theorems of the validation plan, passing the axiom audit.
3. C++ Core export (`--emit-core`) and a conformance harness in which the legacy compiler, the Lean model and the existing fuzz lanes agree.
4. GIR-H, GIR-L, their verifiers and a C emitter behind `--pipeline gir` for the three profiles; every other feature an explicit `unsupported` error.
5. A build-cost report (`--build-report`) that attributes counts, bytes and time to source functions and specialization dimensions, run on a public synthetic family and on Aincrad3.
6. Shared implementations in the legacy backend (`--share`): fewer emitted bodies, every context still checked.
7. Code-generation units with persistent native-object reuse and link skipping (`goose build --units`), single-file output unchanged.
8. The edit-based qualification matrix passing its structural gates, with reuse failure modes handled and dependency prediction shadow-tested.
9. One proved, certificate-checked bounds-check rule on GIR.
10. The linter and bootstrap contracts intact.
11. A final report: claim ledger, Aincrad3 edit-loop table before and after, and every deferred component with its boundary.

## 1. Charter

- Decide, log the call in §10, and keep going. Never ask, never wait for approval, send no progress report. Run until every deliverable is met or every remaining item is parked.
- Hard stops, each of which parks the item and moves on: an action outside this repository other than reading the Aincrad3 checkout; anything §7 forbids; a loop that cannot check anything. Pushing is always forbidden. So are upstream pull requests.
- Fix on the way, in its own commit, what is egregious: a loop command over 5 minutes on a quiet host; a CPU-time regression over 2× against the baseline on a command whose new flags are absent; a test red on the baseline that blocks the item. Record anything else and leave it.
- Parity before optimization. No item of phase P3 starts while a P1 item is neither done nor parked.
- A failing item gets three attempts, each ending in a root-cause statement (`root-cause`); Tier B theorems get two. Then it is parked with a finding, and work continues with whatever does not depend on it.
- Measure honestly. Time-based numbers are taken only when `perf-gate-ready` exits 0 before and after; otherwise write "perf gate deferred: host busy" and continue. A deferred gate never counts as passed and blocks only the close. Structural gates, which count events, always run. No speedup is stated that was not measured, and every number is vetted with `benchmark-checklist`.
- Bookkeeping is minimal: no provenance, hashes or manifests beyond what a deliverable needs.
- Run as wide as file ownership and memory allow (`orchestrate`). Start with four lanes; widen from measured peak memory, keeping 16 GB free. Budget 4 GB for a C++ lane building at `--parallel 4` (the compiler's own build peaked near 2 GB) and 8 GB for a Lean lane. Aincrad3 measurements are run by the integrator alone, one at a time.
- Lanes are `worker`. The lanes proving `TH-SAFE-01` and `TH-LOWER-01` and the theorem-statement reviewer are `expert`. The final adversarial review is `god`.
- Lane worktrees are `.work/wt/<lane>` on branch `goose-ir-<lane>`; each builds in its own `build/`. The integrator verifies merged commits from `.work/wt/verify`. All scratch is under `.work/`, never `/tmp`. After a lane merges and its checks pass on the merged tree, the integrator removes its worktree and deletes its branch; a parked lane keeps its branch.
- Every commit is a Conventional Commit scoped by workstream (`feat(units): …`). Item ids go in the body.
- Code comments never cite this document, its item ids, gates or theorem ids.
- Follow `AGENTS.md`: no formatters on existing `.goose` files; new `.goose` fixtures may be formatted with `scripts/format_goose.py`; `/usr/bin/rg` and `/usr/bin/fd` if the ones on `PATH` fail to execute.

## 2. Decisions

### 2.1 Owner-decided (2026-10-12)

| # | Decision |
|---|---|
| O1 | The campaign ends at profile-bounded GIR/C. Full-language GIR parity, promotion to default, and LLVM are later campaigns. |
| O2 | Where the Lean model and the legacy compiler disagree: explicit language-specification text wins; where it is silent, the legacy compiler's behavior wins. Each disagreement gets a minimized reproducer and an entry in `semantics/decisions.md`. The executor never edits `docs/goose_spec.md`, an existing expected output, or legacy compiler behavior. |
| O3 | Lean and C++ lanes run in parallel against the frozen Core encoding. A feature is reported as supported by GIR only when its Lean semantics runs and conformance passes for it. Proofs gate claim labels, not lane starts. |
| O4 | Sharing, units and reuse land first on the legacy backend through a backend-neutral layer, so Aincrad3 benefits in this campaign. GIR-L feeds the same layer afterwards. |
| O5 | The executor may read and build the local Aincrad3 checkout at a recorded commit. Only aggregate counts, sizes and timings enter this repository. |
| O6 | Build scalability is a primary requirement with its own gates, not a consequence hoped for from the IR. |

### 2.2 Prescribed

Each is settled by the code or by practice; the last column says what would reverse it.

| # | Decision | Reason | Reversed by |
|---|---|---|---|
| P1 | Lean 4.34.1 from `PATH`, no Lake dependencies. | Builds and proves the needed lemma kinds on this host with core only. | A Tier A theorem parked solely for a missing library lemma. |
| P2 | The axiom audit is an allowlist of `propext`, `Classical.choice`, `Quot.sound`. | This Lean gives `bv_decide` and `native_decide` per-theorem axiom names; a denylist cannot name them. | — |
| P3 | One fuel-indexed interpreter per representation is the semantics; no separate relational semantics. | One definition; safety by induction on fuel. | Specification §22. |
| P4 | Nonlocal return targets the innermost active call of a function in the target set; no activation capability. | Language spec §7.9; confirmed on the baseline compiler. | A language change. |
| P5 | Core and GIR are tagged JSON arrays, written by C++ and read only by Lean. | Removes an untrusted-input parser from the compiler; Lean's parser accepts duplicate object keys. | A second reader. |
| P6 | Conformance reuses `fuzz/driver.py` and its lanes. No new generator or reducer. | They exist, run on this host, and carry independent models. | — |
| P7 | The lint facts producer is not refactored. Core export is a second read-only consumer at the same pipeline point. | Facts already come from the checked, unoptimized program. | Core export needing data the checker discards. |
| P8 | New flags are opt-in; every existing command's behavior and default output bytes are unchanged. | Contract. | The owner, after the campaign. |
| P9 | Sharing is equality of canonical lowered bodies; symbols come from stable keys, never from content. | Specification §16.3, §15. | Item `O2`'s gate. |
| P10 | Native reuse is keyed by unit text, headers read and contract. It is called native-unit reuse, never incremental compilation. | Complete by construction; honest about cost (a). | — |
| P11 | Unit-mode runtime additions go in a new header used only by unit output. The five existing runtime files are not edited. | Keeps single-file output and `RuntimeVersion` byte-identical. | A runtime defect that blocks an item. |
| P12 | SHA-256 is implemented in the compiler; no C++ dependency is added. | About a hundred lines; a dependency buys nothing. | — |
| P13 | `.github/workflows` is not edited. CI wiring is listed for the owner. | The executor cannot run CI. | — |
| P14 | Unsupported features on `--pipeline gir` are a compile error with status 1 and the prefix `error: unsupported in pipeline gir: <feature-id>`. | Existing error convention; harnesses classify by prefix. | — |
| P15 | Aincrad3 is obtained with `git archive` of the recorded commit into `.work/aincrad3`; its repository is never written. | Read-only by construction. | — |
| P16 | Review by a non-author is a reviewer lane answering the validation plan's six questions, plus the mechanical witnesses and counterexamples. | No person is available. | — |

### 2.3 Delegated

The executor decides within the bound, takes the smallest reversible option, and logs it.

| # | Decision | Bound |
|---|---|---|
| D1 | Lean definitions, lemma structure, tactics. | The stated theorems; the audit; no `partial`, `unsafe`, `opaque` under a listed theorem. |
| D2 | C++ structure inside `src/core`, `src/gir`, `src/ident`, `src/report`, `src/units`. | Header-only, included from `src/main.cpp`, like the rest of the compiler; listed in `CMakeLists.txt`. |
| D3 | Which legacy fact marks a returned local as the destination local (`C-NAMED`). | Must agree with the frontend's warning. |
| D4 | Unit target size, helper inlining threshold, batch size of native invocations. | Start at specification §17.2's value; set from item `B3`'s measurements; one value each, no flag. |
| D5 | Extra fact rules for bounds certificates. | Each with its soundness lemma. |
| D6 | Fixture names and harness internals. | Python standard library only; stems unique across `test/`. |
| D7 | Handling of the `shrink-exit-exception` and other frontend-accepts, validator-rejects cases. | Report `unsupported`, or extend the rule with its proof. Never accept without proof. |
| D8 | Using `leanchecker` as a second kernel check. | Optional; if used, its exit status is checked, not its silence. |

## 3. Baseline

| Fact | Value |
|---|---|
| Host | Alpine Linux, musl, x86_64, 32 cores, 60 GB; Clang 23.1.3, GCC 15.2.0, CMake 4.3.4; Lean 4.34.1. |
| Known failures | Not yet recorded; item `G0` runs the suites and writes them here. |
| Loop timings | **perf gate deferred: host busy.** Item `G0` records them. |
| Compiler build peak memory | About 2 GB for the largest process of a Debug build. |
| Phase timing in the compiler | None exists. |
| Single-fixture filter in `test/run_tests.py` | None exists; `G0` adds it. |
| Aincrad3 | Available. Commit `ef1e1ef33b96fa68748e4ecf3cad37153a4de59c`, extracted to `.work/aincrad3`; its one generated source file is copied from the checkout's own staged build output. Entry point `src/world-core-continue.goose`. `goose --check` (Debug compiler, `-O1`) reports 14,642 specializations, 8,861 inlined calls, and a 1.5 GB compiler peak. Not a timing baseline. |
| Historical figures (issue #9, 2026-10-11) | 14,575 specializations typechecked; 66,026,053 bytes of C; standalone emission median 43.150 s. Emission only: not native compilation, linking or runtime. Not a baseline; `B1` remeasures. |
| Frozen budgets | The proposed values of validation plan §11, to be replaced here by `B1`. |

Checks already run are listed in validation plan §1. The code facts the design rests on are in specification §14.

## 4. Sequence

Items have a size (S: a session; M: a few; L: many; XL: split by the lane), prerequisites, owned files and an acceptance proof. A lane takes consecutive items of its workstream in one go. `src/main.cpp`, `CMakeLists.txt` and `test/run_tests.py` are shared: lanes only append.

### 4.1 Workstreams

| Workstream | Owns | Items |
|---|---|---|
| `sem-core` | `semantics/Goose/Core/**` except `Num.lean`, `semantics/Main.lean`, `Proofs/{Fuel,Core,Memory,Safety}.lean` | S1, T1, then the Lean parts of S8, S9 |
| `sem-num` | `semantics/Goose/Core/Num.lean`, `Proofs/Num.lean` | T0 |
| `sem-share` | `semantics/Goose/{Share,Reuse}/**`, `Proofs/{Share,Reuse}.lean` | T2 |
| `sem-gir` | `semantics/Goose/{GIR,Lower,Evidence}/**`, `Proofs/{Lower,Bounds,Exit,Construct}.lean` | S7, T3, O1's Lean part |
| `export` | `src/core/**`, `src/gir/**`, `test/compiler_gir.cpp`, `test/gir/**` | S2, S5, S6, then the C++ parts of S8, S9, O1 |
| `conf` | `test/semantics/**`, `fuzz/driver.py` | S3, S4 |
| `backend` | `src/ident/**` except `deps.h`, `src/report/**`, `src/units/**`, `src/build.h`, `src/codegen*.h`, `src/runtime/runtime_units.h`, `test/compiler_ident.cpp`, `test/compiler_units.cpp` | B1, B2, B3, B4, B7 |
| `deps` | `src/ident/deps.h`, recording hooks in `src/typecheck*.h` | B6 |
| `scale` | `test/scale/**` | B5, H2 |

Widest phase: P1, nine workstreams with ready work once `G0`–`G2` land.

### 4.2 P0 — ground (integrator, serial)

| ID | Size | Work | Acceptance |
|---|---|---|---|
| `G0` | M | Build the base compiler at `.work/build/base`. Run the baseline suite, the linter suite and the bootstrap once; write failures and skips into §3. Add `--only GLOB` and a repeatable `--goose-arg ARG` to `test/run_tests.py`. Record loop timings when the host is quiet. | `python3 test/run_tests.py --only 'codegen/evaluation_order*' --profile baseline --cc native` runs that fixture alone; target under 20 s on a quiet host. |
| `G1` | M | `semantics/` skeleton: Lake project, `lean-toolchain`, `Goose/Audit.lean`, `goose-semantics audit`, empty `coverage.json`, `decisions.md`, `trust.md`. Three hand-written Core goldens in `test/semantics/golden/` (issue #9's `first`, the sampled-extent probe, a range loop) per specification §4 and §12: the frozen encoding both `sem-core` and `export` build against. | `(cd semantics && lake build) && semantics/.lake/build/bin/goose-semantics audit` exits 0; the audit fails when a listed theorem is replaced by `sorry`. |
| `G2` | S | `test/scale/gen.py` emitting issue #9's two-context program and its expected counts. `test/scale/parity.py`, which emits C for every fixture and sample at `-O0` and `-O2` with two compilers and compares bytes. Record the Aincrad3 commit and extract it to `.work/aincrad3`, or record it unavailable. | The generated program compiles and prints its expected value on the base compiler; `parity.py` reports no difference for the base compiler against itself and a difference for a deliberately altered one. |

### 4.3 P1 — parity and completeness

Semantic track.

| ID | Size | Prereq | Work | Acceptance |
|---|---|---|---|---|
| `T0` | M | G1 | Numeric definitions and `TH-NUM-01`. | Audit lists `TH-NUM-01`; `NUM-01`–`NUM-06` evaluated examples. |
| `S1` | L | G1 | Lean Core for `core-pilot`: types, memory, `eval`, `validate`, decoder; `goose-semantics run` and `validate`. | The goldens decode, validate and run to their expected output; decoder cases `VER-01`, `VER-08`. |
| `S2` | L | G1 | In-memory Core and `--emit-core FILE` for `core-pilot`: closure conversion, implementation and context tables, effect summaries, `unsupported` errors. No work when the flag is absent. | The goldens' sources export to modules the Lean tool accepts; default emitted C byte-identical to the base (`test/scale/parity.py`). |
| `S3` | M | S1, S2 | `test/semantics/run_tests.py`; the pilot rows of validation plan §6 as fixtures; Lean and Core export as stages of `fuzz/driver.py`. | `python3 test/semantics/run_tests.py --profile core-pilot` all `agree`; 2000 seeded cases each of `scalar`, `numeric`, `order` agree. The 2000-case runs are gate runs taking many minutes; the loop uses `smoke` and `--case`. |
| `T1` | L | S1 | `TH-FUEL-01`, `TH-CORE-01`, `TH-MEM-01`, `TH-MEM-02`, `TH-SAFE-01` for `core-pilot`. | **`G-PILOT`.** |
| `T2` | M | S1 | `TH-ERASE-01`, `TH-SHARE-01`, `TH-SHARE-02`, `TH-REUSE-01`; the quotient checker as an executable (`goose-semantics share`). | Audit lists them; the witnesses and counterexamples of validation plan §4.2. |
| `S5` | L | S2 | GIR-H in C++: data structures, Core lowering, verifier, `--emit-gir-high`. | `test/compiler_gir.cpp` cases `VER-02`–`VER-06`, `VER-09`. |
| `S7` | L | S1 | Lean GIR-H: syntax, `run`, validator, decoder, the Lean lowering. | The C++-exported GIR of every pilot fixture validates and runs to Core's result. |
| `S6` | L | S5 | GIR-L, placement, the C emitter, `--pipeline gir`, `--emit-gir-low`. | Pilot fixtures and lanes agree across legacy, Lean and `gir`, release and debug, native and TinyCC. |
| `T3` | L | S7 | `TH-GIR-01`, `TH-LOWER-01`. | **`G-GIR`** with S6. |
| `S8` | L | G-PILOT, S6 | `core-shrink` through every layer, one slice per workstream; its Tier A theorems. | **`G-SHRINK`**: `MEM-04`–`MEM-07`; `resize`, `reference`, `trap` lanes agree. |
| `S9` | XL | S8 | `core-construction` through every layer; `TH-EXIT-01`; `TH-CON-01` as Tier B. | **`G-CONSTRUCT`**: `CON-*`, `EXIT-*`. |

Build track. It starts at the same time as `S1`.

| ID | Size | Prereq | Work | Acceptance |
|---|---|---|---|---|
| `B1` | L | G0, G2 | Stable keys (`DeclKey`, `TypeKey`, `ContextKey`), SHA-256, phase timers, per-function byte accounting, dimension attribution, `--build-report FILE`. All inert without the flag. Then the integrator runs it on the synthetic family and Aincrad3, writes the counts and phase split into §3, and freezes the budgets. | **`G-ATTR`**: the report passes validation plan §9.2; §3 names the dimensions behind the growth and the split of the loop among costs (a)–(d). |
| `B5` | M | G2 | The synthetic family in full: shareable and must-stay-distinct members, the edit transformations with expected changed sets, `test/scale/edit_matrix.py`, the Aincrad3 runner. | The family's expected checked-context counts match the base compiler; the matrix runner reports `E00` on the single-file path. |
| `B2` | L | B1 | A naming seam in the legacy backend with the existing scheme as default and a stable-key scheme; lowering-key and consumed-assumption recording; canonical-body classes over call-graph components; `--share`. | **`G-SHARE`**: `L-SHARE`; the baseline suite passes with `--goose-arg --share`, which the runner does not apply to its four checks that read the shape of emitted C; default output byte-identical to the base. |
| `B3` | L | B2 | Unit assignment and unit text per specification §17: per-unit declarations, module globals segments, literals by content, location tables, stable nonlocal target ids, the program unit; `--emit-units DIR`. | Every runnable fixture and sample builds from its units and matches its expected output; unit text is identical across two runs and across `-j`. |
| `B4` | L | B3 | `goose build --units`: the store, completion records, locking, parallel batched native compilation, link skip, the recording reader and R0, `--rebuild`, `--verify-reuse`. | **`G-UNITS`**: `L-NOOP`, `L-LEAF`, `L-LOC`, `L-ADD`, `L-EQ` on the synthetic family; first Aincrad3 edit-loop table in §11. |
| `B6` | L | B1 | Dependency sets recorded in the checker under the report flag; invalidation prediction in the report. No reuse acts on it. | Validation plan §10.3's shadow rows: no under-approximation on any matrix edit. |
| `B7` | S | S6, B3 | The GIR-L emitter produces instance text through the unit interface. | Pilot fixtures pass under `--pipeline gir` in units mode. |

### 4.4 P2 — hardening

| ID | Size | Work | Acceptance |
|---|---|---|---|
| `H1` | M | The rest of validation plan §7. | Every row fails at its named layer. |
| `H2` | M | `E10`–`E16`, and the seeded randomized edit sequence under `--verify-reuse`. | **`L-FAIL`**; no divergence from a clean build. |
| `H3` | M | Validation plan §8, including a `--units`-built `goose-lint` run through the linter suite. | `LINT-01`–`LINT-08`. |
| `H4` | M | `docs/implementation.md` and `docs/testing.md` sections for the new flags, the report, sharing, units and the store, in domain terms; `semantics/decisions.md` and `trust.md` complete; §8 complete. | Every command in the docs runs. |

### 4.5 P3 — optimization and polish

| ID | Size | Condition | Work | Acceptance |
|---|---|---|---|---|
| `O1` | L | — | Fact certificates on GIR-H, the C++ pass that proposes them, the Lean checker; `TH-BCE-01`, `TH-CERT-01`. | **`G-BCE`**. |
| `O2` | L | The report shows context-dependent optimization blocking at least 10% of emitted bytes among otherwise-equal instances on Aincrad3, or on the corpus if it is unavailable. | Sharing before optimization (specification §16.5) with its validation mode. | `L-SHARE` still exact; the baseline suite with `--share`; fewer optimizer and emission phases in the report. |
| `O3` | M | — | Set unit size, helper threshold and batch size from measurement; make the frozen budgets gate. | Validation plan §11 on a quiet host. |
| `O4` | M | Emission is at least 20% of `E03`'s wall time on Aincrad3 after `B4`. | Unit-text reuse (R2). | `L-EQ`; fewer units rendered in the report. |
| `O5` | S | — | Measure units with link-time optimization against single-file for a release build. Report only. | A table in §11. |

### 4.6 P4 — close

Delete what the campaign made dead (`dead-code-archaeology`). Run the full baseline suite, the linter suite, the facts-scale case, the bootstrap, the semantics and scale harnesses once more on the merged tree. Run `ultrareview`; fix its P1 and P2 findings. Have the final review done by a `god` lane. Write the validation plan's report into §11. **`G-CLOSE`.**

The full baseline suite runs at `G-PILOT`, `G-SHARE`, `G-UNITS`, `G-GIR` and the close, because each changes code on the legacy path or adds fixtures to it. Between those, an item ends on its own acceptance command.

## 5. When each result is expected

| Result | Gate | What it does and does not show |
|---|---|---|
| Actionable build-cost attribution | `G-ATTR` (`B1`), in parallel with the Lean pilot | Which of costs (a)–(d) dominate, and which dimensions multiply bodies. Changes no cost. |
| Fewer emitted bodies without weaker checking | `G-SHARE` (`B2`) | Reduces (b), and (c) on cold builds. Every context is still checked: (a) is unchanged. |
| Reuse of unchanged native units | `G-UNITS` (`B3`, `B4`) | Reduces (c) and (d) on warm builds. The frontend and emission still run in full after any edit. |
| Reduced frontend recomputation | `G-UNITS` for a no-op build only; prediction tested at `B6` | A build with unchanged inputs runs nothing. After an edit, the frontend runs in full in this campaign. Reuse of checked results is deferral `X2`. |
| Measured improvement to Aincrad3's loop | First table at `G-UNITS`; final at `G-CLOSE` | If the frontend dominates the loop, the improvement is bounded by the native share, and the report says so with the split. |

## 6. Acceptance

| Deliverable | Proof |
|---|---|
| 1 | `(cd semantics && lake build)`; `python3 test/semantics/run_tests.py --profile P` for each profile. |
| 2 | `semantics/.lake/build/bin/goose-semantics audit`; reviewer answers in `semantics/coverage.json`. |
| 3 | `python3 fuzz/driver.py run --lane L --count 2000 --seed 1 --semantics …` for each profile lane. |
| 4 | The same with `--pipeline gir`; `test/compiler_gir.cpp` through `test/run_tests.py`. |
| 5 | `G-ATTR`. |
| 6 | `G-SHARE`. |
| 7 | `G-UNITS`. |
| 8 | `python3 test/scale/edit_matrix.py --workload synthetic` with every structural gate; `H2`. |
| 9 | `G-BCE`. |
| 10 | `H3`; `python3 test/scale/parity.py --goose <candidate> --baseline .work/build/base/goose`. |
| 11 | §11 filled from the validation plan's template. |

## 7. Contract changes

**Pre-authorized, all additive and opt-in:** the flags `--emit-core FILE`, `--emit-gir-high FILE`, `--emit-gir-low FILE`, `--pipeline legacy|gir`, `--build-report FILE`, `--share`, `--emit-units DIR`, and for `goose build`: `--units`, `--rebuild`, `--verify-reuse`; the report format `goose-build-report/1`; the store directories under a program's existing build directory; `src/runtime/runtime_units.h`; `--only` and `--goose-arg` in `test/run_tests.py`; `--semantics` and `--pipeline` in `fuzz/driver.py`; new files in `CMakeLists.txt`'s source list; new entries in the C++ unit-test list.

**Forbidden:** changing the behavior or default output bytes of any existing command; facts v1, diagnostics v1, contracts v1, lint configuration, baselines, lint statuses, warning text; `docs/goose_spec.md`; existing fixtures and expected outputs; the five existing runtime files; the checker's acceptance of any program; `.github/workflows`; a new dependency in C++ or Lean; making any new mode the default; `master`.

Each change made is appended to §8.

## 8. Contract changes made

*(append-only; one line per change: what, where, why)*

## 9. Non-goals and deferrals

Dropped, not queued: LLVM emission; MLIR; a JIT change; memory SSA; stack sharing between slots; a C++ reader for Core or GIR; persistence of Core or GIR across compiler versions; a module or package system with separate checking; new language syntax; linter rule changes; CI changes.

Deferred, each with its boundary:

| # | Component | Boundary now | Reason | Prerequisite | Follow-on acceptance |
|---|---|---|---|---|---|
| `X1` | Checking a body once against root parameters instead of once per context | The production checker is unchanged; cost (a) per context remains | A redesign of the checker's specialization machinery | `B1`'s share of check time; `TH-SAFE-01`; `B6` | Diagnostics on `test/errors_tc` identical; contexts checked on the synthetic family fall from contexts to implementations plus call-site checks; lint fanout unchanged |
| `X2` | Reuse of checked results after an edit | Dependency sets are recorded and predicted, never acted on | Unsound without proven-complete dependency recording | No under-approximation across the matrix and randomized sequences on both workloads; frontend at least half of `E03`'s wall time on Aincrad3 | Contexts checked per edit within the predicted set; `L-EQ`; identical diagnostics |
| `X3` | GIR for the whole language; a GIR-built `goose-lint`; promotion | Three profiles, opt-in | O1 | This campaign's close | Every runnable fixture, sample and the bootstrap under `--pipeline gir` |
| `X4` | Units, sharing or stable names as the default | Opt-in | P8 | Owner's decision on §11 | The baseline suite and bootstrap under the new default |
| `X5` | Stored references, optionals, ADTs, pools, relative references, floats, threads | `unsupported` | Each needs its own semantics and proofs | The profile before it | Its fixtures, lanes and Tier A theorems |

Reducing emitted bytes is not a success criterion by itself, and native-unit reuse is never described as incremental compilation.

## 10. Reference

### 10.1 Architecture

```text
source + imports + compile-time resources
                |
   parse / resolve / typecheck / specialize          (a) frontend
        every context checked; lint facts here
                |
      +---------+----------------------------+
      |                                      |
 legacy optimizer, BCE                  Typed Goose Core --> Lean: validate, eval, proofs
      |                                      |
 legacy lowering to C text               GIR-H + verifier + evidence
      |                                      |
      |                                  GIR-L + verifier
      |                                      |
      +----------------+---------------------+
                       |
        instances (stable symbols, canonical bodies)
                       |
        shared implementations                       (b) emitted code
                       |
        units  --or--  single file (default)
                       |
        native objects, reused by key                (c) native compile
                       |
        link, skipped when unchanged                 (d) link and driver
```

### 10.2 What must not break

The linter builds its facts from the checked program before optimization and spawns the Goose-native `goose-lint` beside the compiler (`src/main.cpp:1430-1500`). Its warning consensus, root-depth contexts, suppression and baseline identities, offline behavior, coverage and statuses 0–4 are release contracts. `specialization_fanout` counts checked, entry-reachable contexts. CMake builds `goose-lint` from single-file C emitted by the just-built compiler (`CMakeLists.txt:98-108`); that stays. The Goose-in-Goose bootstrap compares stage-2 and stage-3 C byte for byte (`test/run_tests.py:1158-1193`). Four tests read the shape of single-file C (`test/run_tests.py:1600-1661`).

### 10.3 Risks

| Risk | Control | Signal that parks the item |
|---|---|---|
| The model proves a different language | O2; fixtures per ordering rule; the fuzz lanes' independent models | An unresolved disagreement on a profile feature |
| A shared body is unsafe in one context | Equality of lowered bodies; `TH-SHARE-01`; the must-stay-distinct family | A divergence between `--share` and unshared output |
| A reused object is stale | Content keys; `--verify-reuse`; the randomized edit sequence | Any `L-EQ` failure |
| Units make the program slower or the cold build worse | Measured budgets; single-file retained for release | A frozen budget missed after `O3` |
| Legacy backend changes alter default output | `test/scale/parity.py` at every gate | Any byte difference |
| Proof work expands without end | Tiers; time-boxes; parked theorems keep their lemmas | Attempts exhausted |
| Normal `check` and `lint` get slower | Everything inert without its flag; `LINT-06` | The 2× threshold of §1 |

## 11. Results

*(written at each gate from the validation plan's template; the Aincrad3 tables hold aggregates only)*

## 12. Decision log

*(append-only; one line per judgment call: the call and why)*

- Aincrad3's core entry imports a source file that its build generates and does not track. Copied it from the checkout's existing staged build output instead of running its generator, which reads another private repository: reading the checkout is within O5, the generator's input is not.
- The checker already groups roots into classes: one helper called with many distinct globals and many locals at different depths gets two specializations, not one per call site. The synthetic family therefore has to vary the dimensions that do multiply specializations; `B1`'s dimension attribution on Aincrad3 says which those are, and `B5` builds its members from that.

## 13. Campaign log

*(append-only; one line per gate or phase end)*

- `G2` merged: `test/scale/gen.py` (issue #9's program, parameterized) and `test/scale/parity.py` (1,120 emissions compared; base against itself equal, `--no-bce` differs in 696).

## 14. For the owner afterwards

- §11's attribution: whether the frontend or native compilation dominates Aincrad3's loop decides whether `X1` and `X2` are the next campaign.
- §8 and `semantics/decisions.md`: every contract change and every disagreement with the legacy compiler.
- `semantics/coverage.json`: theorems passing, parked, and the reviewer's answers.
- Whether to make units or sharing the default (`X4`), and whether to wire the Lean build and the scale harness into CI (P13).
- Parked items, each with its finding and branch.
