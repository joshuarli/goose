# Campaign: Lean-backed Goose semantics, then Goose IR

**Status:** implementation campaign; no implementation or proof is claimed by this document.  
**Design revision:** 0.1, 2026-10-12.  
**Repository:** `joshuarli/goose`.  
**Working branch:** `goose-ir`.  
**Audited base:** `62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a`.  
**Primary deliverable:** an executable, mechanically checked semantic foundation followed by an opt-in, backend-neutral IR pipeline with C parity and preserved fork tooling. LLVM is a subsequent, separately gated experiment.

## Reading order

This campaign defines sequencing, integration, deliverables, and acceptance. Read the [provisional Goose IR specification](goose-ir-spec.md) for the proposed representations and verifier contract, and the [proof and validation plan](goose-ir-validation.md) for theorem obligations, fixtures, measurements, and release gates. Together these are one implementation brief.

The current language remains defined by [the Goose specification](../goose_spec.md). This campaign proposes implementation architecture, not a replacement language specification. Conflicts must be resolved through the semantic decision process below, never by silently changing accepted programs or rewriting expected outputs.

## 1. Executive decision

Build a small Lean 4 definition of **Typed Goose Core**, an executable reference interpreter, and selected safety and transformation proofs before implementing the production GIR migration. Use that foundation to design and validate **Goose IR (GIR)**. Retain the existing frontend, existing C path, runtime, TinyCC execution, and Goose-native linter throughout the experiment.

The first milestone that justifies the experiment is not a hello-world Lean project. It is a distinctly Goose fragment with grow-only storage, aliases, snapshots, checked indexing, lexical cleanup, executable comparisons against the current C backend, a reference-validity theorem, and a small bounds-check-elimination theorem. Construction destinations and nonlocal returns follow before GIR becomes a supported alternative pipeline.

The target architecture is:

```text
source + imports + compile-time resources
                |
     canonical C++ frontend
     parse / resolve / typecheck / specialize
                |
       immutable semantic snapshot
         /                     \
        v                       v
 existing lint-facts v1       Typed Goose Core
        |                  /          |          \
 Goose-native linter      /      Lean reference   existing AST path
                  independent       model             |
                  Core validation     |               C
                         |            |
                         +----> GIR-H + verifier
                                    |
                    language-aware transforms
                                    |
                     storage / exit lowering
                                    |
                              GIR-L + verifier
                               /           \
                              C       optional LLVM
                              |             |
                       existing runtime + native tools
```

The diagram expresses responsibility boundaries, not a requirement to copy the entire AST for every command. Ordinary checking and linting must not pay for unused GIR construction. Core is the source-side meaning boundary; GIR-H and GIR-L are stages in one IR family. The production C++ compiler does not move to Lean. LLVM does not become Goose's semantic source of truth.

### Non-negotiable rules

1. Preserve Goose's intentional aliasing and type-safe reuse. Compiler-internal linear capabilities are not new source-language borrowing restrictions.
2. Preserve defined release behavior, required failures, evaluation ordering, reference identity, and the in-place construction contract with its actual exceptions.
3. Never call a tested C++ implementation verified merely because a similar Lean function was proved correct.
4. Never trust an imported `safe`, `noalias`, `in_bounds`, `balanced`, or `pure` flag without the validation required by the relevant claim.
5. Keep lint source-oriented, offline by default, and independent of optimized GIR. No second parser or typechecker in the linter.
6. Keep `master` unchanged during this experiment. Do not remove the old pipeline or silently fall back within a partially supported function.
7. Do not make Lean, LLVM, or a source checkout runtime dependencies of an ordinary shipped Goose/linter installation.
8. Report unsupported features, timeouts, and unknown analyses explicitly. An incomplete run is not a clean result.

## 2. Repository baseline and implications

The following observations are anchored to the audited base, not the older revision discussed during preliminary design. They are source/document inspection findings; the compiler and suites were not executed while preparing this campaign.

| Existing component | Observed contract | Campaign consequence |
|---|---|---|
| `src/codegen.h` and `codegen_*.h` | C generation consumes optimized `FnSpec::body`; representation, destinations, hidden stack arguments, nonlocal return channels, and watermark cleanup are intertwined with emission. | Extract decisions into explicit Core/GIR operations incrementally. Keep existing runtime representations initially. |
| `src/lint_facts.h` | Private frontend/linter boundary; original-node spans, normalized paths, type/root specialization contexts. | Preserve source identity and context independently of GIR numbering. |
| `docs/lint/facts-v1.md` | Closed-shape JSONL protocol with ordered records, validation, limits, explicit coverage, terminal count/integrity. | GIR must not be smuggled into this protocol. A protocol extension requires versioned producer/consumer changes. |
| `tools/lint/main.goose` | The current Goose-native companion implementation is in this file. | Do not mistake the modular paths proposed in `linter.md` for existing files. Splitting this implementation is optional, separate work. |
| `CMakeLists.txt` | Build `goose`, emit standalone C for `tools/lint/main.goose`, compile `goose-lint` with the project's C compiler, install both together. TinyCC is bundled by the current build. | Keep an explicit legacy-C bootstrap path; later test a GIR-built companion without creating a build dependency cycle. Do not copy obsolete build-option recipes. |
| `src/type_queries.h` | `StableTypeGraph` only queries completed, stable concrete type graphs and avoids instantiation. | Reuse this distinction at the snapshot boundary; serialization must not mutate/infer types. |
| `docs/testing.md` | Native/TinyCC, debug/release, sanitizers, bootstrap, linter, resource paths, and runtime-cache tests already exist. | Extend the existing runners and packaging tests rather than inventing a parallel disconnected quality system. |
| `docs/design/analysis_inventory.md` | Historical analysis inventory at `bfea86b`, including overlapping storage/effect models. | Reconcile with current code first. Its counts and recommendations are not a current defect list; current tests already include root-set laws. |

Primary repository evidence: [code generation][R1], [lint implementation contract][R2], [facts protocol][R3], [build][R4], [tests][R5], [stable type graphs][R6], [historical inventory][R7].

### Preserve the fork, not just upstream Goose

The fork's product includes `goose lint`, the adjacent `goose-lint` executable, structured compiler warnings, contracts, suppression and baseline semantics, honest specialization coverage, deterministic output, offline package handling, packaging, Unicode/CRLF spans, and linter scale tests. These are release gates, not optional polish.

Read `AGENTS.md` before each implementation tranche. Preserve existing `.goose` formatting and deliberately malformed fixtures. Use small reviewable commits. Respect the repository's no-`git push` convention; publication is a separate maintainer-authorized action. This document delivery creates a documentation-only branch; it does not authorize upstream PRs, default-branch changes, dependency upgrades, or broad cleanup.

## 3. Scope, boundaries, and proof vocabulary

### 3.1 What the campaign will deliver

An executable Core semantics; a bounded conformance oracle; selected kernel-checked theorems; independently checked Core/GIR artifacts for supported fragments; a versioned GIR schema and verifier; a C emitter consuming GIR-L; opt-in CLI integration; language-aware transformations whose evidence is explicit; preserved linter behavior and packaging; measured comparison with the legacy pipeline; and a documented decision on promotion or retention as an experiment.

An LLVM AOT prototype follows only after the GIR/C gates. A whole-language safety proof, verified frontend, verified native runtime, fully verified LLVM backend, new language syntax, source-language ownership redesign, MLIR adoption, Cranelift backend, new JIT, general autofixer, and language server are not prerequisites or implied deliverables.

### 3.2 Claim levels

Every feature and theorem in the coverage ledger uses one of these labels:

| Label | Meaning |
|---|---|
| `specified` | Reviewed prose and formal definition exist for the stated fragment. |
| `executable` | A reference implementation exists with tests and explicit limits. |
| `model-proved` | Lean checks a theorem about named definitions and assumptions. |
| `instance-checked` | A documented checker validates this concrete artifact/transformation; its execution and integration trust are stated. |
| `implementation-proved` | A theorem or justified reuse path actually connects the production implementation to the modeled behavior. |
| `differential-tested` | Named compiler configurations agree on a recorded corpus. Not a universal theorem. |
| `assumed` / `deferred` / `unsupported` | The boundary is explicit; no stronger claim is made. |

A formal semantics alone proves no compiler correct. Kernel acceptance establishes a theorem relative to its statement, definitions, and assumptions; statement review remains essential. CompCert is useful precedent for expressing semantic-preservation guarantees with explicit compilation boundaries, not a claim that Goose receives those guarantees by analogy. [E1, E2]

### 3.3 Initial trust boundary

The pilot assumes the canonical parser, resolver, typechecker, and specialization process have produced a candidate typed Core artifact. An independent Core validator checks the supported artifact's structural, typing, initialization, lifetime, and effect obligations. Exported annotations are evidence requests, not axioms. This still does not prove that parsing or elaboration preserves surface-source meaning.

The executable oracle's compiled binary depends on Lean's compiler/runtime, its input decoder, host execution, and trace plumbing. Kernel-checked theorem claims have a different trust boundary. Keep those rows separate. C/LLVM correctness, runtime allocation/guard-page behavior, FFI, OS services, and hardware remain outside initial theorems.

Finite storage is explicit in the model. A theorem conditioned on sufficient capacity is labeled accordingly. Harness fuel exhaustion is `inconclusive`; semantic divergence is not inferred from a timeout.

## 4. Semantic charter before migration

Assign stable requirement IDs to existing clauses without renumbering the language spec. Start with:

| ID | Contract | Initial treatment |
|---|---|---|
| `SEM-EVAL-01` | Left-to-right evaluation; values snapshot when evaluated, references preserve views rather than contents. | Core execution rule and event-order fixtures. |
| `SEM-EVAL-02` | Index/slice receiver region and extent are sampled before index/bounds expressions; assignment resolves destination first. | Explicit Core nodes and GIR snapshot operations. |
| `SEM-NUM-01` | Exact-width integer semantics; signed/unsigned interpretation; mandatory versus debug-only failures. | Bitvector definitions with Goose-specific guards. |
| `SEM-MEM-01` | Permitted growth preserves existing reference validity; it need not preserve contents mutated through aliases. | First memory theorem. |
| `SEM-MEM-02` | Scope reclamation and permitted shrinking leave no usable reference into reclaimed/retyped storage. | Initial lexical-scope fragment; expand to shrink and interprocedural rules. |
| `SEM-MEM-03` | Limited/reusable slots may remain valid after logical removal/reuse. | No invented generation checks that reject legal stale references. |
| `SEM-CON-01` | Fresh nonfixed values construct into receiving storage; only specified staging/relocation exceptions are allowed. | Destination and construction-event model. |
| `SEM-CON-02` | Whole resizable assignment clears before constructing and prohibits forbidden RHS access to the old owner. | Static obligations plus runtime ordering. |
| `SEM-EXIT-01` | Nonlocal return targets the correct dynamic invocation and cleans intervening scopes without destroying surviving results. | Activation-aware control semantics. |
| `SEM-REP-01` | Packed layout, relative-reference targets, initialization, and byte-visible representations agree. | Later byte-level refinement, not assumed from abstract typing. |
| `SEM-OBS-01` | Required failures and external effects are preserved; debugging instrumentation has its stated latitude. | Observation profiles and preservation relations. |
| `TOOL-LINT-01` | Existing diagnostic IDs, evidence, suppression identity, statuses, coverage, and offline behavior survive. | Black-box and facts-level compatibility. |

The current numeric spec has unusual rules worth testing explicitly: signed `%` is Euclidean; shifts mask counts; `i64.min / -1` always aborts while narrower signed minimum/-1 follows debug-overflow versus release-wrap rules; `as` range-checks in debug, while `as!` does not; floating conversion details are separately specified. Do not import C, LLVM, or library defaults. [R8]

### Decision ledger

Create `semantics/decisions.md` with: ID, source clause and revision, competing interpretations, minimal programs, current compiler observations, proposed formal meaning, compatibility impact, resolution owner, and evidence links. Initial entries must cover debug-overflow optimization latitude; bounded construction staging; returned-local destination exceptions; balanced grow-shrink calls; root-set joins; dynamic nonlocal targets; relative-reference relocation; finite-reservation failure; and source/IR diagnostic identity.

Freeze a small **semantic profile**, not the entire evolving language. An unresolved question blocks only the feature depending on it. The legacy compiler remains available for the rest. A disagreement does not automatically favor the old compiler or the new model: minimize it, consult the spec, review the decision, then change code or specification explicitly.

## 5. Workstreams and ownership

Use four accountable roles, even when one person fills several: language/spec owner; semantics/proof owner; compiler/backend owner; tooling/validation owner. A non-author reviews theorem statements and compatibility-affecting decisions. Each work item has one owner, a named reviewer, dependencies, acceptance commands, evidence location, and rollback condition. Names are assigned at kickoff rather than invented here.

Suggested new paths, all **proposals until implemented**:

```text
semantics/
  lean-toolchain
  lakefile.toml
  lake-manifest.json
  Goose/Core/{Syntax,Types,Memory,Effects,Step,Eval,Validate}.lean
  Goose/Proofs/{Eval,References,Cleanup,Bounds,Lowering}.lean
  Goose/GIR/{Syntax,Validate,Step}.lean
  Goose/Certificates/Bounds.lean
  Main.lean
  coverage.json
  decisions.md
  trust.md
src/core/                     # C++ typed snapshot/export adapters
src/gir/                      # C++ IR, verifier, analyses, lowering
src/gir/c/                    # GIR-L C emission; existing runtime reused
src/gir/llvm/                 # optional later target, not required initially
test/semantics/               # paired Core/source cases and harness
test/gir/                     # valid/invalid modules and lowering cases
```

Keep existing `test/` category discovery rules intact. New nested fixtures need deliberate runner integration, unique stems, and manifests. Follow the current header/translation-unit conventions initially; changing the compiler build architecture is a separate measured change.

## 6. Milestones and acceptance gates

```text
M0 baseline + contracts
  -> M1 executable Lean Core
  -> M2 proved Goose pilot + C conformance   [first decision gate]
  -> M3 destinations, exits, shared semantic snapshot
  -> M4 GIR-H/GIR-L + verifiers + lowering
  -> M5 GIR -> C semantic and tooling parity [migration gate]
  -> M6 selected GIR optimization + evidence
  -> M7 release qualification / promotion decision
  -> M8 optional LLVM AOT experiment
```

Linter baselining starts in M0, source-identity work runs alongside M1-M3, and compatibility gates apply at every milestone. Draft IR design may evolve during Lean work; production lowering must not run ahead of the semantic contract for its feature.

### M0 — Baseline, branch hygiene, and semantic inventory

**Dependencies:** none. **Owners:** compiler and validation; spec review.

**Work:**

- Verify branch ancestry and record the exact compiler base, spec hash, dependency locks, CMake options, compiler/runtime versions, OS/libc/kernel/architecture, target profile, and available optional packages.
- Run the documented baseline and linter suites; inventory real results, skips, and failures. Capture ordinary warning text, structured lint output, suppression/baseline behavior, and install layout before editing frontend data structures.
- Reconcile `analysis_inventory.md` against current roots, effects, type-query APIs, and their tests. Do not reintroduce an old model or redo an already-completed root-set refactor.
- Inventory all specification clauses and AST/codegen operations. Assign each to the first supported Core/GIR profile or an explicit later gate.
- Establish observation profiles, numeric truth tables, and the initial decision ledger. Pin Lean and minimal dependencies by exact versions; do not use a moving `latest` in CI.
- Add a documentation/coverage checker that rejects missing statuses and links. Establish separate proof, conformance, and performance result locations.

**Artifacts:** baseline manifest; behavior snapshots; semantic requirement map; decision ledger; toolchain policy; supported-fragment manifest.

**Gate G0:** a clean worktree baseline is reproducible, existing failures are recorded, mandatory numeric/observation decisions for the pilot are resolved, and no runtime/default behavior changed. Documentation is not a substitute for executing this milestone.

### M1 — Lean Core syntax, execution, and independent validation

**Dependencies:** G0. **Owners:** semantics; compiler adapter support.

Implement a small typed, structured Core independent of C strings and `FnSpec` pointers. Use stable variable/function/type IDs, explicit binding/value distinctions, lexical scopes, evaluation contexts, and reference provenance. Define abstract typed memory with initialized-slot information, root instances, backing regions, and finite capacities. Implement integers/bools, local variables, aliases, grow-only arrays of fixed elements, snapshot indexing/slicing, branches, loops, and initially nonrecursive direct calls.

Define a small-step relation with observable labels and explicit outcomes. Write a fuel-bounded executable stepper and decoder; malformed input and unsupported operations are not program traps. Provide finite evaluator soundness/completeness relative to the step relation. Add a validator that checks supported Core artifacts without relying on C++ pointer identity or unexamined safety booleans. Use conservative rejection in the experimental importer when it cannot validate an obligation, with an explicit unsupported explanation; do not change normal Goose acceptance.

Implement manually authored Core fixtures first. Add source-to-Core export from an immutable, pre-optimization snapshot second. Differential agreement of the two representations is test evidence, not a proof of surface elaboration.

**Artifacts:** Lean project; Core schema/profile; evaluator; validator; paired fixtures; trace decoder; initial claim/trust ledger.

**Gate G1:** supported fixtures execute in Lean; malformed/unsupported inputs fail explicitly; fuel exhaustion is distinguishable; evaluator correspondence theorems check; annotations cannot bypass validation; source checking/linting remain unchanged.

### M2 — First useful proof package and existing-backend conformance

**Dependencies:** G1. **Owners:** semantics and validation.

Prove preservation of the pilot memory invariant under permitted growth and lexical cleanup, plus no invalid memory access for the supported, validated fragment under stated environment assumptions. Include an alias that remains valid but observes a changed value, and negative cases whose rejection is necessary for the theorem.

Prove one real BCE rule: a sampled index is within a sampled extent, and subsequent permitted growth preserves validity of the selected existing element. Include exact-width arithmetic and effect invalidation conditions. Do not start by porting the entire `bce.h` solver. A small checked witness format is preferred where it provides a real connection to actual C++ decisions; its proof must not assume the conclusion in its inputs.

Run source fixtures through the legacy C/native and TinyCC paths and compare against the reference model. Add model-driven generation for valid and invalid programs and reduction to small counterexamples. Distinguish agreement, mismatch, unsupported, harness failure, and inconclusive.

**Artifacts:** named theorems with dependency audit; reproducible comparison report; generator/reducer; a semantic decision or transformation contract constrained by the work.

**Gate G2:** reference validity, cleanup, evaluator correspondence, and the selected BCE theorem are checked; the pilot corpus agrees under its observation policy; deliberate bad transformations are detected; a reviewer confirms non-vacuity and source relevance. Only now approve production GIR implementation. Retaining the executable model with the old C backend is an acceptable outcome if GIR has no demonstrated value.

### M3 — Construction, nonlocal exits, and source semantic snapshot

**Dependencies:** G2. **Owners:** semantics/compiler; linter review required.

Add explicit receiving destinations, nested construction, initialization order, construction restrictions, permitted internal layout moves, bounded-receiver staging exceptions, returned-local behavior, and abrupt construction abandonment. Add activation-aware nonlocal return semantics, cleanup ownership, result-destination survival, nested targets, and recursive target cases. Fixed-mode versus variable-mode ADTs, limited arrays, grow-shrink restrictions, and reusable slots receive separate coverage rows and fixtures as introduced.

Do not define a universal rollback transaction: Goose construction may leave permitted external effects and already-completed earlier elements. Each operation specifies which destination prefix becomes visible and what cleanup applies. Ordinary runtime abort does not imply source-level destructors or exception cleanup.

Extract or adapt an immutable semantic snapshot: original source identity, stable completed types, checked specialization contexts, root alternatives, source-level call/result shapes, and conservative effect summaries. Preserve the old facts producer's behavior through an adapter. Snapshot creation must not instantiate types, mutate warning consensus, execute target code, build native sidecars, or fetch imports in ordinary lint mode.

**Artifacts:** extended semantics/proofs; destination and exit decision records; source snapshot API; lint compatibility fixtures; GIR draft revised from actual proof experience.

**Gate G3:** the model handles the migration's defining construction/exit contracts; linter output and source checks remain compatible; no new exclusive-reference assumption is introduced; all unsupported categories remain explicit.

### M4 — GIR representation, verifiers, and semantic lowering

**Dependencies:** G3. **Owners:** compiler/semantics.

Implement [GIR 0.1](goose-ir-spec.md): typed CFGs, scalar SSA/block parameters, explicit places, source origins, effect summaries, snapshots, construction capabilities, exit targets, and stage-specific operation legality. Implement readable dumps, deterministic serialization, bounded parsers, roundtrips, verifier diagnostics, and negative-module tests before optimization.

Implement Core-to-GIR-H lowering without reusing C syntax as an intermediate. Define the state relation and a stuttering simulation for the supported fragment. Prove a small representative lowering in Lean and state precisely whether the production lowering is only differentially tested or concretely checked. Type-correct GIR by itself does not establish source preservation.

Implement GIR-H-to-GIR-L storage/cleanup lowering incrementally. Reuse existing runtime layouts and ABI decisions where practical. Make logical roots distinct from physical stack slots; scopes with disjoint lifetimes may share storage only after validated planning. Preserve reverse-order cleanup and surviving caller destinations. Do not remove AST optimizations wholesale: retain them on the legacy path and migrate their useful language-specific effects in isolated tranches.

**Gate G4:** valid modules roundtrip deterministically; invalid modules cannot manufacture capabilities/facts; representative Core and GIR executions agree; cleanup paths are explicit; all passes revalidate; claim coverage is honest. No default pipeline change.

### M5 — GIR-to-C parity, linter dogfooding, and bootstrap

**Dependencies:** G4. **Owners:** compiler and tooling/validation.

Write a real C emitter consuming GIR-L. It must not convert GIR back into `FnSpec::body` and invoke the old AST code generator. Reuse scalar/runtime helper definitions, packed layouts, runtime files, build/package drivers, and conservative ABI wrappers; move only the necessary representation planning behind a shared interface.

Introduce opt-in selectors with explicit errors for unsupported profiles. Proposed names are `--pipeline=legacy|gir`, `--emit-core`, `--emit-gir=high|low`, and `--verify-gir`; they do not exist at this document revision. Keep existing meanings of `-o`, `--standalone`, `--jit`, `--check`, `--multi-test`, `goose run`, `goose build`, and `goose lint`. `--check` and normal lint must not require GIR or Lean.

Build the bundled companion with the legacy path by default during the pilot. Once its language features are supported, also compile `tools/lint/main.goose` through GIR/C and run the same public linter suite against both companion builds. Test all supported producer/companion combinations, protocol-version mismatch, relocated installations, and no-source-checkout operation. GIR host compiler selection must not accidentally invoke lint while building the linter or require the companion to compile itself.

Extend the existing Goose-in-Goose regression without promoting its subset frontend into a semantic authority. Its existing stage-to-stage fixed-point tests remain intact; generated-C byte equality between different top-level backends is not required.

**Gate G5:** full supported runtime/source/lint corpus passes; no silent partial fallback; packaging and companion bootstrap work; actual default-rule finding identities/statuses/coverage are preserved; self-lint and scale checks pass; performance is measured. Every existing language feature needed for promotion is either supported or remains explicitly restricted to the opt-in experiment.

### M6 — Selected language-aware optimizations

**Dependencies:** G5. **Owners:** compiler/semantics.

Start with check elimination and redundant length/header reload elimination under validated effects. Then consider cleanup coalescing, destination propagation, and stack-top caching. Each transformation includes its exact preconditions, a counterexample family, model proof or checked-instance path where practical, C++ integration tests, and a cost measurement. Generic low-level optimization remains the native backend's job.

Reuse existing root/effect infrastructure after reconciliation rather than maintaining a new fourth competing alias model. Analysis summaries use conservative joins and call-graph fixpoints; unknown effects do not become empty sets. Separate root lifetime bounds from exact object identity and disjointness. Construction capabilities justify only the restricted operation they represent, not blanket `restrict` or LLVM `noalias` on source references.

**Gate G6:** measurable benefit or demonstrable simplification for at least one real workload; no unexplained benchmark regression; transform provenance and invalidation are testable; the proof-implementation connection is accurately labeled. Keep any unqualified optimization disabled.

### M7 — Release qualification and promotion decision

**Dependencies:** G6. **Owners:** all four roles.

Complete the existing-language feature matrix for a production default, or explicitly ship GIR as experimental. Cover globals and initialization order, recursion, generics/function values, ADT representations, all array modes and pools, relative references and serialization, full numeric/float behavior, FFI, threads, optional native packages, runtime/resource paths, and installed artifacts. Formal coverage may remain narrower than implementation/test coverage; expose both.

Run the release matrix in [the validation plan](goose-ir-validation.md). Publish a claim ledger, known limits, evidence bundle, rollback command, and measured tradeoffs. A default change is a distinct reviewed decision, not a side effect of merging a refactor. Retain legacy selection through at least one explicitly chosen compatibility cycle. Removing it later requires a separate proposal.

**Gate G7:** product parity and supported-target qualification are complete for the intended release status. Fewer emitted C lines or the existence of proofs is not sufficient. A no-go decision preserves useful Lean/Core work and a documented experimental branch.

### M8 — Optional LLVM AOT experiment

**Dependencies:** G5 at minimum for development; G7-quality coverage for promotion. **Owners:** backend and validation.

Start with one explicit target/toolchain pair and ordinary LLVM IR plus existing C runtime/interop wrappers. No custom LLVM fork, new GC, replacement allocator, JIT, or simultaneous Cranelift/MLIR effort. Pin the LLVM release and target data layout. Keep external aggregate ABI lowering behind tested adapters.

Compare against Clang's IR from the GIR/C path and the legacy/C path. Study what information or lowering quality is actually improved. Preserve mandatory traps, actual alignment, pointer validity, and arithmetic wrapping; do not emit unproved optimization attributes. LLVM's own frontend guidance recommends learning from the IR shapes its optimizers handle well. [E3, E4]

**Gate G8:** semantic and tooling qualification on the declared target plus a demonstrated benefit. Direct LLVM emission is optional even if the Lean/GIR campaign succeeds.

## 7. Linter migration contract

### 7.1 Preserve the existing interface

Keep the public diagnostics v1, facts v1, contracts v1, config, suppression, and baseline contracts stable unless a dedicated versioned change is approved. The current facts reader rejects unknown keys; adding optional fields without changing the protocol is not backward compatibility. The facts integrity hash detects accidental corruption and is not an authenticity mechanism. The protocol's compiler revision field currently identifies the runtime version, not a Git SHA. Do not use it as the sole GIR/proof cache identity. [R2, R3]

Preserve exit statuses: 0 completed/no denied finding; 1 denied finding; 2 source/import error; 3 CLI/config/policy/baseline error; 4 tool/protocol failure or required incomplete coverage. Preserve missing-companion behavior, closed-schema validation, resource caps, owner-only temporary files, and cleanup. Existing source warning messages outside lint mode retain their text and consensus behavior.

### 7.2 Preserve source facts before optimization

Use original-node identity and source spans to anchor warnings and statements. GIR operation IDs, specialization numbering, basic-block order, backend selection, or inlining must not change finding fingerprints. Keep source call shapes and argument evaluation order before lowering to CFG. A typed semantic operation may acquire multiple origins after optimization; it must not manufacture a new source suppression site.

In particular, `unused_pure_value` must not disappear just because GIR deletes the expression, `post_overflow_guard` must see the original typed arithmetic/check relationship, `stale_slice_length` must retain its documented conservative abstention, and `specialization_fanout` must report checked entry reachability rather than optimized surviving function count. Contract-based rules retain exact callee/owner identities and receiver argument numbering. Unsupported generic/reachability cases remain incomplete rather than clean. [R2]

### 7.3 Reuse semantics without replacing lint policy

Introduce a shared read-only fact vocabulary for roots, effects, types, snapshots, and call results only when it simplifies the existing producer. Keep rule selection, contracts, confidence, suppressions, baselines, and rendering in Goose. No Lean process runs during ordinary linting. Optional proof-backed findings require their own evidence classification and supported-shape tests; they do not enable deferred rules automatically.

Before migrating a rule, record old/new fact records and normalized findings for its positive cases, legitimate counterexamples, aliases, generic contexts, source line shifts, and unsupported patterns. Do not automatically regenerate user baselines to hide changes. Preserve finding identity under a compiler implementation refactor; explicitly document any necessary fingerprint-version migration and require a deliberate baseline rewrite.

### 7.4 Tooling completion gate

Run `test/lint/run_tests.py`, the separate `facts_scale.py`, relocated-install tests, concurrency tests, corrupted-protocol tests, all existing-rule snapshots, and self-linting. Preserve the twelve shipped rule behaviors and all dispositions in the 65-ID inventory; do not interpret registration as implementation. Any changes to the root-depth specialization context must be tested for warning consensus, fanout counting, and baseline drift. [R2, R5]

## 8. Proof engineering and change discipline

Pin Lean/dependency revisions. Keep specification modules free of production C++ state and host-dependent behavior. For release-gating theorems, maintain an explicit list of declarations and inspect transitive axioms; reject unfinished proofs, custom axioms that assert desired properties, and unreviewed native-computation trust. Prefer kernel-checkable evidence; audit the mechanisms of the pinned Lean version rather than assuming a historical axiom name. Recheck artifacts in clean CI, with an independent reviewer reading the actual theorem statements and definitions. Lean's validation documentation explains both dependency auditing and rechecking. [E1]

Every theorem has a scope, assumptions, relation, positive witness, negative fixture, and production connection. Property tests and finite enumeration support non-vacuity; they do not replace proofs. Every program generator and minimizer preserves or revalidates the category it claims to generate.

Keep logical memory safety distinct from object-level business identity. A reusable slot reading a new same-typed value is legal Goose behavior, not a memory-safety counterexample. Keep behavioral traces distinct from construction/resource traces: equal stdout does not justify forbidden staging. Do not prove exact wall-clock performance.

Lean-MLIR is relevant precedent for SSA/region rewriting proofs, but adopting its framework is a design option, not a dependency of this campaign. Review reusable ideas against the chosen Core/GIR contracts before adding a dependency. [E5]

## 9. Suggested commit-sized backlog

Each row is an implementation changeset or small series, not a claim of current completion.

| ID | Work package | Depends on | Required evidence |
|---|---|---|---|
| `W00` | Baseline manifest, source/lint snapshots, semantic ledger | none | G0 report |
| `W01` | Lean toolchain, Core IDs/types/numeric profile | W00 | boundary truth tables, lock/rebuild |
| `W02` | Memory, small-step relation, executable evaluator | W01 | trace fixtures, evaluator correspondence |
| `W03` | Core validation and immutable export adapter | W02 | malformed artifacts, acceptance boundaries |
| `W04` | Growth/cleanup proofs and BCE pilot | W03 | axiom/non-vacuity report, mutation tests |
| `W05` | Differential harness/generator/reducer | W02-W04 | minimized reproducible corpus; G2 |
| `W06` | Destination, partial construction, abrupt exit model | W04 | construction/target fixtures and proofs |
| `W07` | Shared source snapshot and lint v1 adapter | W00, W03 | old/new facts and finding identity |
| `W08` | GIR schema, serializer, high-stage verifier | W06-W07 | roundtrip/negative verifier suite |
| `W09` | Core-to-GIR-H and semantic comparison | W08 | lowering relation and labeled evidence |
| `W10` | Region planning, cleanup, GIR-L verifier | W09 | lifetime/cleanup/representation cases |
| `W11` | GIR-L C emitter, opt-in driver, runtime adapters | W10 | supported semantic parity |
| `W12` | Companion dogfood, bootstrap, packaging matrix | W07, W11 | linter and installed-artifact reports |
| `W13` | Checked BCE integration and effect invalidation | W11-W12 | transform evidence and performance |
| `W14` | Remaining feature/target parity | W11-W13 | complete release coverage ledger |
| `W15` | Promotion/no-go record and rollback qualification | W14 | G7 evidence bundle |
| `W16` | Optional LLVM target prototype | G5 minimum | G8 report, no default change |

A commit that changes language acceptance, facts protocol, numeric policy, or claim scope requires an explicit decision record in the same review. Rebase/merge current `master` into the experiment in dedicated integration commits, rerunning G0 comparisons; do not silently move the audited base inside prior evidence.

## 10. Measurements, risk controls, and rollback

Measure frontend, snapshot/export, Core/GIR validation, each lowering/pass, C/LLVM emission, downstream compilation/linking, total build time, peak RSS, emitted code/object size, runtime, and source-diagnostic costs separately. Measure ordinary `goose check` and lint independently of GIR runs. Use identical workloads/flags, warmups, alternating baseline/candidate runs, repeated samples, environment records, and variation reporting. Do not infer common-case speed from a pathological stress test. [R5, R9]

Proposed review triggers, to be calibrated and frozen at G0: more than 5% reproducible median regression on a representative normal check/lint workload, more than 10% peak-RSS growth, or more than 5% runtime regression on a representative kernel requires an explicit tradeoff decision. These are proposed engineering budgets, not measured results or universal release thresholds. No correctness regression is traded for performance. Stress-path improvement never exempts the normal workload.

| Risk | Control | Stop/rollback condition |
|---|---|---|
| Model proves a different language | Clause IDs, examples, independent statement review, source comparisons | Unresolved disagreement on a covered contract |
| Safety assumed in annotations | Recomputed validation or sound checked evidence | Untrusted metadata can remove a check |
| Formalization expands indefinitely | Small profiles, G2 decision, separate deferred rows | No real compiler decision constrained by pilot |
| IR duplicates AST with C strings | Explicit semantic operations and a real GIR-L emitter | New backend still requires old AST emission |
| Source tooling loses fidelity | Pre-optimization snapshot and identity tests | Existing finding/suppression/coverage regression |
| Alias model accidentally becomes Rust-like | Legal alias/reuse witnesses in every affected gate | Existing valid program rejected for new exclusivity |
| Cleanup drops results or leaks partial storage | Activation-aware destinations, path verifier, state traces | Nonlocal target/destination mismatch |
| Old compiler bug becomes oracle truth | Independent model and reviewed spec decisions | Expectations changed without adjudication |
| Toolchain trust expands invisibly | Separate proof/execution ledgers and dependency pins | Unreviewed native axioms or runtime assumptions |
| Default compiler becomes heavier | Opt-in lazy construction; timing/RSS gates | Normal check/lint pays material unused-IR cost |

Rollback is selecting the legacy pipeline and disabling individual experimental transformations, not reverting user source or baselines. Preserve old fixtures and result artifacts. Unsupported GIR operations produce an explicit experimental-pipeline error; no best-effort emitted native code. A partially supported backend is never selected implicitly by installed tooling.

## 11. Final definition of done

The mandatory campaign is complete when the executable Core and claim ledger are maintained in CI; the first useful safety/transformation proofs are checked; the Core/GIR boundary is independently inspectable; GIR/C implements its declared feature profile; the fork's linter, bootstrap, runtime, and packaging pass their gates; normal-path costs and benefits are measured; and a reviewer records a promotion or experimental-retention decision with an operational rollback.

A production-default migration additionally requires complete implementation and test coverage of the existing supported language and targets. It does not require pretending that every feature is formally proved. LLVM is a separate extension, not the success criterion.

**The objective is an executable specification and a compiler architecture that must provide evidence for preserving it—not a large proof directory disconnected from the compiler.**

## Sources and evidence

Repository sources below are pinned to the audited base. Design recommendations elsewhere in this document are proposed work, not facts inferred from those sources. The historical linter campaign `linter.md` is context; current `docs/lint/*`, source, and tests are the implementation contract.

[R1]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/src/codegen.h
[R2]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/lint/README.md
[R3]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/lint/facts-v1.md
[R4]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/CMakeLists.txt
[R5]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/testing.md
[R6]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/src/type_queries.h
[R7]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/design/analysis_inventory.md
[R8]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/goose_spec.md#62-integer-semantics
[R9]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/AGENTS.md

External primary references, consulted 2026-10-12; implementation must pin compatible versions rather than depend on moving documentation:

- **E1:** [Lean: validating proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
- **E2:** [CompCert: semantic preservation and verification boundaries](https://compcert.org/man/manual001.html).
- **E3:** [LLVM: performance tips for frontend authors](https://llvm.org/docs/Frontend/PerformanceTips.html).
- **E4:** [LLVM language reference](https://llvm.org/docs/LangRef.html) and [undefined behavior manual](https://llvm.org/docs/UndefinedBehavior.html).
- **E5:** [Verifying Peephole Rewriting in SSA Compiler IRs](https://arxiv.org/abs/2407.03685).
