# Goose semantics/GIR: proof, conformance, and qualification plan

**Revision:** 0.1, 2026-10-12.  
**Status:** required future work; no results or completed proofs are asserted here.  
**Baseline:** `62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a`.  
**Companions:** [campaign](goose-ir-campaign.md), [provisional IR specification](goose-ir-spec.md).

## 1. Evidence contract

Every result must name the exact source/compiler/spec revision, Core/GIR schema, semantic and numeric profiles, target/runtime ABI, executable/toolchain versions, command, input/corpus identity, environment, result classification, and artifact location. A successful tool exit is insufficient when coverage is incomplete.

Use separate records for `specified`, `executable`, `model-proved`, `instance-checked`, `implementation-proved`, `differential-tested`, and `assumed/deferred/unsupported`. The same feature may have broad implementation/test coverage and narrow proof coverage. Never collapse these columns into one green badge.

Every supported source fixture has a requirement ID, expected accept/reject decision, source clause, expected observable behavior or allowed behavior set, applicable profiles, and a reason for exclusions. Every theorem has a statement, assumptions, proof dependency report, witness examples, negative/mutation cases, and its production implementation connection. Every benchmark has raw samples and a declared comparison method.

Proposed evidence layout:

```text
semantics/coverage.json
semantics/trust.md
semantics/decisions.md
test/semantics/cases.json
test/gir/cases.json
build/evidence/<base>-<candidate>/
  environment.json
  commands.jsonl
  proofs/                 # declaration list, dependency/recheck reports
  conformance/            # outcomes, traces, minimized mismatches
  lint/                   # facts, public findings, install/scale results
  performance/            # raw samples, summaries, uncertainty
  coverage.json
  decision.md
```

Generated results live outside source control unless a deliberate, bounded report is useful. Reproducers and expectation changes belong in source control; host paths, private input content, and enormous raw logs do not.

## 2. Required theorem program

Names below are theorem targets, not Lean declarations already present. Mathematical prose specifies intended meaning; the implementation must supply actual definitions and reviewed statements.

| ID | Intended statement | Scope/assumptions and non-vacuity |
|---|---|---|
| `TH-EVAL-01` | A finite successful executable evaluation corresponds to the small-step relation with the same observations; every finite modeled execution can be replayed with sufficient fuel. | Supported Core profile and validated decoder. Fuel exhaustion is not divergence. Include loops and both normal/abort outcomes. |
| `TH-CORE-01` | Acceptance by the independent Core validator establishes the stated Core well-formedness and initial invariant. | Does not prove surface parsing or elaboration. Include artifacts with forged root/effect/initialization annotations that must be rejected. |
| `TH-NUM-01` | Each supported numeric primitive implements the Goose width/sign/profile truth table. | Guard total library operations explicitly. Exercise zero divisors, minima, negative remainder, and masked counts. |
| `TH-MEM-01` | Executing permitted growth preserves validity and target identity of every relevant prior reference. | The growth rule's premises must follow from validation; do not assume the resulting state is valid. Include legal alias writes that change contents. |
| `TH-MEM-02` | Lexical reclamation preserves the live-state invariant and leaves no subsequently usable reference into genuinely reclaimed/incompatibly reused storage. | Quantify over semantically live/reachable values. Do not accidentally forbid legal stale limited/reusable references. |
| `TH-SAFE-01` | Executions of validated pilot Core cannot perform an invalid typed memory access; each reachable nonterminal state steps or has a defined external interaction/outcome. | Fixed declared environment and finite-resource policy. Not an all-Goose or all-runtime claim. Include nonempty allocating/calling programs. |
| `TH-BCE-01` | Replacing a checked access with the proven form under its validated index, snapshot, lifetime, and effect premises preserves behavior. | Include wraparound, alias mutation, shrink and unknown-call counterexamples. A proof of the final inequality alone is insufficient. |
| `TH-CERT-01` | If the certificate checker accepts a concrete removal proposal for the actual module/profile, the selected transformation meets the modeled preservation contract. | Reconstruct premises from the module. State whether checker execution and C++ plumbing are trusted or proved. Reject changed operands, stale snapshots, and altered effects. |
| `TH-CON-01` | Supported construction satisfies the receiving-storage event contract, initialization/evaluation order, and publication/abandonment rules. | Explicit permitted relocation, bounded staging, returned-local exceptions. Equal stdout alone is insufficient. |
| `TH-EXIT-01` | Nonlocal exit selects the proper active target, cleans precisely the exited scope resources, and preserves transferred result destinations. | Distinguish source function from dynamic activation, including recursive/nested cases. No assumption that cleanup was already correct. |
| `TH-GIR-01` | The GIR validator establishes the invariants claimed for the supported stage/profile. | Specify which of types, SSA, storage, effects, construction, and exits are actually checked. Do not name a type-only verifier a memory-safety proof. |
| `TH-LOWER-01` | The modeled Core-to-GIR lowering simulates source execution under a stated memory/control relation and preserves required observations. | Administrative stuttering is allowed but needs a progress/rank argument. Production C++ lowering remains separately classified. |
| `TH-LOWER-02` | Supported GIR-H storage/exit lowering preserves the high-stage semantics and construction obligations. | State runtime-helper and layout assumptions. Include every exit edge of a pending construction. |
| `TH-REP-01` | Supported abstract places/values correspond to initialized byte layouts and decoded relative-reference targets. | Later extension. Packing, overlap, null encodings, link widths, and relocation cannot be assumed from nominal typing alone. |
| `TH-DIV-01` | The supported lowering does not introduce infinite internal-only stuttering and preserves the intended divergence/productivity relation. | Separate from termination-only equivalence. Fuel tests provide examples, not this theorem. |

For the first decision gate G2, require `TH-EVAL-01`, pilot validator/numeric obligations, `TH-MEM-01/02`, the supported safety result, and `TH-BCE-01`. Certificate integration can follow once there is a real production transformation to validate. Construction/exit/lowering/representation theorems grow with their feature gates rather than appearing as empty generic claims.

### Review questions for every proof

Can its assumptions be satisfied by an interesting real Goose program? Does it assume the safety/result property in a hidden predicate? Does a called function's supposedly pure summary actually follow from its body? Are source acceptance, final bytes, reference identity, mandatory failures, and construction costs confused? Does the theorem apply to the production algorithm or only a model? Could a changed typeclass, notation, imported axiom, or opaque definition alter its intended statement?

Maintain an allowlist for release-gating proof dependencies and a clean recheck policy for the pinned Lean version. Unsupported/native-computation trust requires a separate reviewed claim level. An optimized native oracle binary and a kernel-checked theorem are not the same trusted system. Lean's [proof-validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) is the reference for version-specific auditing mechanisms.

## 3. Observation and comparison policy

For the closed deterministic pilot, compare exact return values, ordered externally visible effects, mandatory failure kind and source origin, and semantic reference/layout observations. Preserve existing diagnostic wording where existing commands promise it; normalize only declared nonsemantic fields such as a relocated workspace prefix. Do not strip the operation, source location, or failure reason that would expose a regression.

Maintain a second instrumented construction/resource trace: destination identity, initialization order, explicit copies, permitted intra-destination moves, bounded staging, publication, cleanup ownership, and surviving roots. Compare these against a contract, not exact counts of native helper instructions. Do not include irrelevant allocator addresses or scheduler timing in ordinary behavior equality.

Profiles:

| Profile | Comparison |
|---|---|
| Release, deterministic pilot | Exact observable behavior and mandatory failure ordering. |
| Debug, no source optimization | Exact source-operation checks for supported cases. |
| Optimized debug | Mandatory checks exact; signed-overflow instrumentation follows the source spec's allowed transformation latitude. Record expected variation explicitly. |
| Representation tests | Byte equality only for language-defined bytes; exclude unspecified padding. Validate relative targets and source structural equality separately. |
| Finite storage | Same declared capacity or explicit capacity precondition. Exhaustion behavior is separate from semantic invalid access. |
| Concurrency/FFI extensions | Reviewed environment/scheduler contract or allowed trace set, not naive equality of host interleavings. |

A harness timeout, killed subprocess, malformed log, missing backend, capped output, or unsupported feature is never a pass. Report a seed, input hash, command, and preserved artifacts for each mismatch. Tests execute deliberately selected fixtures in isolated work directories; ordinary lint never runs the target program.

## 4. Semantic regression matrix

Each row is a fixture family, not just one happy-path test. Add a positive case, a boundary case, and a case that detects an incorrect transformation. Reuse existing category fixtures where they already cover the requirement.

| ID | Scenario | Required observation |
|---|---|---|
| `NUM-01` | Every integer width/sign at add/sub/mul boundaries | Exact-width wrap or applicable debug failure; no backend promotion. |
| `NUM-02` | Zero divisor in live and discarded expressions | Mandatory abort is not dead-code-eliminated; earlier effects retain order. |
| `NUM-03` | `i64.min / -1` and narrower minimum/-1 | i64 always aborts; narrower case follows debug/release policy. |
| `NUM-04` | Negative dividend/divisor Euclidean remainder, including minimum%-1 | Nonnegative remainder; minimum%-1 is zero; no overflowing absolute-value intermediate. |
| `NUM-05` | Counts -1, 0, width-1, width, width+1 at different count widths | Masked shifts and correct signed right shift. |
| `NUM-06` | `as`/`as!`, same-width sign changes, narrowing, widening | Debug-only range checks and always-unchecked conversion distinguished. |
| `NUM-07` | Optimization regrouping of signed arithmetic | Release identical; optimized-debug result judged under approved instrumentation policy. |
| `NUM-08` | Later float profile: NaN, signed zero, conversion rounding, finite out-of-range values | Source-defined numeric/equality behavior; unresolved infinities handled by decision gate, not guessed. |
| `ORD-01` | Index expression grows sampled array | Check against old sampled extent, even when new index fits current extent. |
| `ORD-02` | Index/bounds expression mutates another object or rebinds owner variable | Original receiver retained; permitted effects occur once and in order. |
| `ORD-03` | Value argument followed by alias mutation; reference argument followed by mutation | Earlier value is a snapshot; reference observes current allowed contents. |
| `ORD-04` | Compound assignment with RHS changing target/value | Resolve destination and read old value before RHS. |
| `ORD-05` | Short-circuit RHS can abort or mutate | No unauthorized speculation or extra evaluation. |
| `ORD-06` | Counted loop versus array iteration that changes length | Preserve each source loop kind's sampling/reread semantics. |
| `MEM-01` | Reference retained through repeated grow-only pushes | Same target remains valid, including through a permitted alias. |
| `MEM-02` | Growth callback mutates an old element | Reference valid; value may change. Safety proof must allow this. |
| `MEM-03` | Inner-scope storage escaping through direct and nested holders | Existing illegal cases rejected; no usable dangling reference. |
| `MEM-04` | Grow-shrink with live slice/ref and last-use-before-shrink | Reject forbidden shrink; accept supported safe ordering without adding exclusivity. |
| `MEM-05` | Balanced grow-shrink call versus unbalanced call, including recursive summaries | Preserve caller view validity; summary fixpoint cannot trust an unfinished body. |
| `MEM-06` | Limited-array pop then retained-reference read then push | Legal same-typed stale reference remains valid. |
| `MEM-07` | Reusable slot/free/reallocate, and slice-pool reuse | Source-valid stale reads and invalid free bounds distinguished. |
| `MEM-08` | Two roots share a physical stack at disjoint lifetimes; overlapping live roots | Safe reuse only with validated placement. |
| `MEM-09` | Multi-root reference join, field read-back, unknown alias call | No dropped alternative enables a bogus check elimination. |
| `MEM-10` | Length/byte-size/reservation arithmetic at finite limits | Required check before out-of-range allocation/write, including release. |
| `CON-01` | Nested function/branch returns constructing into `push` destination | No arbitrary staging; initializer executes once. |
| `CON-02` | Variable-width length prefix changes after construction | Allowed internal movement; correct bytes and link targets. |
| `CON-03` | Limited receiver with unknown-length result that fits/does not fit | Only authorized staging; no write beyond capacity before failure. |
| `CON-04` | Constructor tries to grow or shrink the destination through an alias/call | Reject exact forbidden case; unrelated owner remains legal. |
| `CON-05` | Fixed-value argument evaluation versus relative-bearing/nonfixed in-place push | No new blanket construction restriction changes valid source acceptance. |
| `CON-06` | Whole-resizable assignment with old-owner access in RHS/global/capture | Existing rejection rules and clear-before-build semantics retained. |
| `CON-07` | First versus alternate returned locals and abandoned partial result | Exact return-copy/destination exceptions, not universal free move. |
| `CON-08` | Append completes earlier elements, then constructor exits nonlocally | Publication/abandonment matches reviewed operation policy; no invented all-or-nothing rollback. |
| `CON-09` | Explicit overlapping copy | Source memmove-style result and initialization safety. |
| `EXIT-01` | Fallthrough, break, continue, ordinary return from nested scopes | Correct reverse cleanup; no unhandled temporary root. |
| `EXIT-02` | Nonlocal exit across multiple active constructors/calls | Intended result survives; only abandoned local storage reclaimed. |
| `EXIT-03` | Nested targets with same function identity under recursion | Correct dynamic activation, not first matching static function ID. |
| `EXIT-04` | Target result uses caller-owned storage while callee locals share runtime stacks | No reset past surviving result destination. |
| `EXIT-05` | Runtime abort during construction | Defined abort; no fictional destructor/unwinding requirement. |
| `REP-01` | Packed unaligned fields and nested variable elements | Correct offsets/alignment and traversal. |
| `REP-02` | Fixed/variable ADT modes, payload references, variant overwrite | Source-valid reference and overwrite restrictions preserved. |
| `REP-03` | Self-relative and pool-relative links; null and range edges | Correct scheme, root identity, representable offset, and target. |
| `REP-04` | Permitted relocation/copy of link-bearing values | References retain intended target; forbidden copies rejected. |
| `REP-05` | Serialization roundtrip plus hostile tags/lengths/links | Later profile validates bytes before treating them as values. |
| `INT-01` | Globals, initialization order, imports, compile-time resources | Correct initialization/effect order and dependency identity. |
| `INT-02` | Generics, function values, captures, specialization contexts | Same resolved semantics and warnings; no AST-origin loss. |
| `INT-03` | FFI scalar/pointer and later aggregate ABI cases | Correct platform adapter and explicit effects. |
| `INT-04` | Threads, queues, per-instance globals, lifecycle | Declared concurrency/runtime contract; no accidental shared mutable state. |

The actual source rules for arithmetic, evaluation, arrays, construction, and returns come from [the pinned specification][R1]. Where a current behavior/spec disagreement is discovered, record a decision and reproducer before changing an expectation.

## 5. IR verifier and adversarial-artifact matrix

These are malformed compiler artifacts, not arbitrary new source programs. Each must fail at the appropriate validation layer without producing native code counted as successful.

| ID | Mutation |
|---|---|
| `VER-01` | Missing/duplicate IDs, unresolved symbols/types, unsupported opcode or feature, wrong schema/stage. |
| `VER-02` | Non-dominating SSA use, bad block argument type/arity, branch into unentered scope, illegal backedge capability. |
| `VER-03` | Load before initialization, wrong field type/offset, access with invented alignment, illegal copy of self-relative storage. |
| `VER-04` | Forge disjoint roots, drop a provenance alternative, mark unknown call pure, omit shrink effect. |
| `VER-05` | Duplicate construction token, omit finish/abandon, stage for an ordinary fresh growable result, reset a caller destination. |
| `VER-06` | Forge target capability, match by static ID across activations, return wrong payload, bypass escape cleanup. |
| `VER-07` | Change certificate subject/index/extent/profile after checking; move use beyond invalidating mutation. |
| `VER-08` | Unknown/duplicate JSON key, oversized integer/record/table, excessive nesting, truncated/trailing data. |
| `VER-09` | Source origin out of range, incorrect precision, synthetic node masquerading as a suppression statement. |
| `VER-10` | Target/runtime ABI mismatch, unresolved high operation in low stage, unsupported raw external contract. |

Roundtrip tests compare canonical structured artifacts and semantics, not arbitrary whitespace in a pretty printer. Mutation tests must establish that a deliberately unsafe transform is detected by a verifier, proof checker, or independent oracle rather than simply disabled by unrelated parsing failure.

## 6. Linter compatibility matrix

The current implementation contract is in [docs/lint/README.md][R2], [facts v1][R3], and the [testing guide][R4]. Test producer and companion separately; the tool is not only a formatter.

| ID | Contract |
|---|---|
| `LINT-01` | Same three existing warning IDs/text and per-source specialization consensus under ordinary compiler commands and lint mode. |
| `LINT-02` | Same twelve shipped rule behaviors, default/opt-in selection, legitimate counterexamples, and all 65 inventory dispositions. No deferred rule silently becomes enabled. |
| `LINT-03` | Same resolved call/result shapes, member receiver index, root-depth contexts, and incomplete-reachability treatment. |
| `LINT-04` | Original statements/comments and exact or line-precision spans survive Core/GIR construction. Check tabs, UTF-8, CRLF, raw strings, and synthesized nodes. |
| `LINT-05` | Suppressions bind the same statement; stale/unknown/malformed directives still diagnose; reasons and suppressed findings remain visible. |
| `LINT-06` | Baseline fingerprints survive irrelevant compiler changes and line shifts under the existing algorithm; semantic drift is visible; writes remain explicit and atomic. |
| `LINT-07` | Output ordering and JSONL bytes deterministic under identical sources/options; optimization must not erase source findings or alter fanout to mean emitted functions. |
| `LINT-08` | Statuses 0/1/2/3/4, `--require-complete`, missing companion, incompatible protocol, malformed config, and error envelopes unchanged. |
| `LINT-09` | Default offline imports; `--allow-fetch` does not execute target/native sidecars; embedded resources follow existing checking policy. |
| `LINT-10` | Closed facts schemas, count/hash framing, limits, invalid references, temporary-file safety, and fail-closed reader remain enforced. |
| `LINT-11` | Legacy-built and GIR/C-built companions give the same rule results; supported producer/reader versions tested explicitly. |
| `LINT-12` | Relocated install without checkout/Python/Lean/LLVM: adjacent compiler, companion, stdlib; Unicode/spaces; concurrent runs and cleanup. |
| `LINT-13` | Self-lint `tools/lint/main.goose` and run scale workload after changes to snapshot/producer/reader/context encoding. |
| `LINT-14` | Normal check/lint time and RSS do not acquire unused GIR/Lean work; no dependency cycle while building the companion. |

Do not “fix” compatibility by regenerating every expected JSON file or baseline. Findings with a reviewed semantic correction get focused expectation changes with the decision ID. Preserve full source coverage information even when GIR covers only a subset.

## 7. Execution matrix and commands

### 7.1 Existing commands to retain

The following are existing documented entry points; run them in a properly provisioned checkout and record actual results. They were not run to prepare this document.

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug
cmake --build build --parallel
python test/run_tests.py --profile baseline --cc native --require-clang
python test/lint/run_tests.py --goose build/goose
python test/lint/facts_scale.py --goose build/goose
python test/run_tests.py --goose-in-goose-only --exe build/goose --cc native
```

Adjust executable locations for multi-configuration/Windows builds according to the existing runner, and use the checked-in CI/AGENTS requirements for supported toolchains. Do not silently reuse obsolete optional-package/TinyCC CMake flags. Optional packages and sanitizer profiles must be provisioned and their skips reported using the existing testing guide.

The ordinary CMake build already includes `goose-lint`; preserve that default. The scale suite is separate because it is substantially larger than the focused rule suite. Do not make every local edit run every large stress case, but require the scale evidence before changing the relevant production contracts.

### 7.2 Proposed entry points to implement

These commands describe deliverables, not currently available commands:

```sh
# After adding the Lean project and named executable:
(cd semantics && lake build)
(cd semantics && lake exe goose-semantics --self-test)

# After implementing the campaign harnesses/selectors:
python test/semantics/run_tests.py --goose build/goose --profile core-pilot
python test/gir/run_tests.py --goose build/goose --pipeline gir
python test/semantics/audit_claims.py
```

Choose final option names in the implementing commit and update all three documents and CI together. The harnesses must emit machine-readable coverage/results and fail on mismatches, malformed artifacts, or required unavailable configurations. A consciously excluded/deferred profile is recorded, not falsely run.

### 7.3 Required configurations

Cross independently: Goose optimization level, generated-C optimization level, runtime debug instrumentation, and legacy versus GIR pipeline. The pilot matrix includes O0 and O2, selected mixed optimization combinations, native Clang/GCC where supported, and TinyCC. A C-only bug can otherwise masquerade as Core/GIR agreement.

Retain Linux/macOS/Windows product coverage and the existing sanitizer jobs. Add AOT LLVM configurations only for explicitly supported target/toolchain pairs. Compile/runtime environment, resource capacity, and external input must match when comparing behavior. Do not run a benchmark under sanitizers and compare its time to a nonsanitized baseline.

### 7.4 CI layering

Presubmit: document/schema consistency, changed profile proofs, small conformance and malformed-artifact suites, normal source/linter regressions. Scheduled/full qualification: clean proof recheck, broader generated corpus, sanitizers, full native/TinyCC matrix, scale test, bootstrap and installed-artifact matrix. Release: complete supported target/profile matrix and the promotion/rollback decision bundle.

These are proposed CI jobs, not requests to schedule background tasks. Keep build/test permissions minimal; proof metaprograms and build inputs run in the normal restricted CI environment, not with repository secrets. Dependency changes receive review. Cache hits do not bypass semantic/version validation.

## 8. Performance qualification

Use the existing benchmark corpus, representative valid source programs, linter self-analysis, the documented facts-scale case, and targeted construction/BCE kernels. Pin input sizes and maintain both normal and stress cases. Do not quote historical README speedups as new measurements.

For each comparison, use identical machine/toolchain/flags and workloads, warm both variants, alternate repeated runs, and publish samples, medians, dispersion, and peak memory. Choose sample count after measuring noise; record it rather than hiding it in a summary. Separate startup from steady-state work where meaningful.

Measure frontend/typecheck, snapshot creation, validation, each GIR pass, C/LLVM emission, downstream compilation/linking, total build time, peak RSS, object/code size, runtime, and linter latency independently. Check that removing one C parsing stage does not simply move more work into GIR validation or LLVM optimization.

The campaign's 5% time/runtime and 10% RSS review triggers are provisional budgets to calibrate at G0, not proven thresholds. A benchmark loss must be visible even when a geometric-mean summary improves. Preserve common-case measurements alongside pathological-case wins, following [AGENTS.md][R5].

## 9. Go/no-go checklist by milestone

| Gate | Required evidence before proceeding |
|---|---|
| G0 | Exact baseline and toolchain; actual existing-suite status; numeric/observation pilot decisions; linter snapshots. |
| G1 | Executable Core, bounded decoder/evaluator, independent validation, evaluator correspondence, honest support profile. |
| G2 | Non-vacuous growth/cleanup/safety/BCE proof package; source/C oracle comparisons; deliberately bad transform detected; relevance review. |
| G3 | Construction and target-activation contracts exercised; original source/fact identities preserved; unsupported features listed. |
| G4 | GIR roundtrips, negative verifier suite, representative lowering simulation/evidence, explicit cleanup and no fabricated proof flags. |
| G5 | GIR/C supported semantic parity, linter/companion/packaging/bootstrap gates, no silent partial fallback, measured costs. |
| G6 | Selected optimization evidence connected to actual code, effect invalidation tests, representative benefit or justified simplification. |
| G7 | Intended release feature/target coverage, claim ledger, limitations, rollback qualification, explicit promotion or experimental-retention decision. |
| G8 | Optional LLVM target correctness and tooling parity plus measured benefit; no presumed speedup from emitting IR directly. |

## 10. Completion and result reporting template

Every milestone report should contain:

```text
Milestone / exact base and candidate:
Implemented features and profiles:
Model-proved declarations and assumptions:
Production implementation connection:
Commands actually run and environment:
Passed / failed / unsupported / skipped / inconclusive counts:
Minimized discrepancies and semantic decisions:
Linter/source compatibility changes:
Performance samples and limitations:
Remaining feature/proof boundaries:
Promotion decision and rollback procedure:
```

A fully populated report may conclude that GIR remains experimental. That is preferable to removing unknowns from the report. The campaign succeeds by making semantic obligations executable and compiler changes accountable to evidence; it does not require claiming an end-to-end verified compiler.

## Pinned repository references

[R1]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/goose_spec.md
[R2]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/lint/README.md
[R3]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/lint/facts-v1.md
[R4]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/testing.md
[R5]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/AGENTS.md
