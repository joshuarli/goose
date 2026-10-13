# Goose semantics, GIR and build scalability: proof, conformance and qualification plan

**Revision:** 0.2, 2026-10-12.
**Status:** required work; no result or proof is asserted here except the checks listed in §1.
**Baseline:** `62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a`.
**Companions:** [campaign](goose-ir-campaign.md), [specification](goose-ir-spec.md).

## 1. What was checked while writing this plan

Run on 2026-10-12, Alpine Linux, musl, x86_64, Clang 23.1.3, a Debug build of the baseline compiler. None of these is a timing.

| Check | Result |
|---|---|
| Lean 4.34.1 with Lake 5.0.0 builds a zero-dependency library and executable on this host | Built and ran. |
| Core-only lemmas of the kind TH-NUM-01 and TH-MEM-01 need (Euclidean remainder range, signed wrap range, push preserves an indexed read) | Proved with `omega` and core lemmas; axioms `propext`, `Classical.choice`, `Quot.sound` only. |
| Axioms introduced by `bv_decide`, `native_decide`, `sorry` in this Lean | A per-theorem axiom `<name>._native.bv_decide.ax_*` and `<name>._native.native_decide.ax_*`; `sorryAx`. Not a single fixed axiom name. |
| `Lean.Json.parse` on an object with a duplicate key | Accepted silently. |
| `fuzz/driver.py smoke` for lanes `scalar`, `numeric`, `order`, `resize`, `trap`, `reference` | 8 of 8 cases each, no failure. |
| Sampled-extent indexing, growth preserving an alias, Euclidean `%`, masked shift (specification §4.5, §5) | Baseline compiler behaves as specified. |
| Innermost-activation target of `return … from` under recursion (specification §7.2) | Baseline compiler behaves as specified. |

Not checked: any timing; the full baseline suite; Aincrad3; `leanchecker`'s exit status on a real project.

## 2. Claim levels

| Label | Meaning |
|---|---|
| `specified` | Prose and a formal definition exist for the stated fragment. |
| `executable` | A reference implementation runs, with stated limits. |
| `model-proved` | Lean checks a theorem about named definitions under stated assumptions. |
| `instance-checked` | A checker validated this concrete artifact. |
| `implementation-proved` | A theorem connects the production implementation to the model. Not expected in this campaign. |
| `differential-tested` | Named configurations agree on a recorded corpus. |
| `assumed`, `deferred`, `unsupported` | The boundary is stated; no stronger claim is made. |

A feature has one row per label in `semantics/coverage.json`; labels are never merged into one status. A theorem about a Lean function is a claim about that Lean function. The C++ implementation is `differential-tested` or, where a Lean checker runs on its output, `instance-checked`.

## 3. Lean project rules

- Toolchain: Lean 4.34.1, found on `PATH`. `semantics/lean-toolchain` records the version, and the audit command fails if `lean --version` disagrees.
- Dependencies: none. `lake-manifest.json` has an empty package list. Mathlib and Batteries are not used; a missing lemma is proved locally.
- Axioms: every theorem in `Goose/Audit.lean`'s list depends only on `propext`, `Classical.choice` and `Quot.sound`. The audit is an allowlist: any other axiom fails it, which covers `sorryAx` and every `._native.` axiom without naming them. `bv_decide` and `native_decide` are therefore unavailable to listed theorems.
- Definitions used by listed theorems are not `opaque`, `partial`, `unsafe` or `implemented_by`.
- The executable oracle is compiled Lean and is trusted separately from kernel-checked theorems; the trust ledger has a row for each.

```text
semantics/
  lakefile.toml  lean-toolchain  lake-manifest.json
  Goose/Core/{Types,Syntax,Num,Memory,Eval,Validate,Json}.lean
  Goose/GIR/{Syntax,Eval,Validate,Json}.lean
  Goose/Lower/CoreToGir.lean
  Goose/Evidence/Bounds.lean
  Goose/Share/Quotient.lean
  Goose/Reuse/Model.lean
  Goose/Proofs/{Num,Fuel,Core,Memory,Safety,Share,Reuse,Lower,Bounds,Exit,Construct}.lean
  Goose/Audit.lean
  Main.lean                      -- goose-semantics
  coverage.json  decisions.md  trust.md
```

## 4. Theorem program

Statements are targets. The Lean statement that is finally proved is recorded beside each in `coverage.json`; if it is weaker than the target, the row says how.

**Tier A** is required for the campaign's proof deliverable. **Tier B** is attempted within the item's time-box and otherwise parked with its proved lemmas and a finding.

### 4.1 Core

| ID | Tier | Statement | Non-vacuity |
|---|---|---|---|
| `TH-FUEL-01` | A | `eval n p m = done o t → n ≤ k → eval k p m = done o t`, and `eval` is a function, so results are unique. | A looping program times out at every fuel; a terminating one is `done` from some fuel on. |
| `TH-NUM-01` | A | Each integer primitive meets its row of specification §5, stated over mathematical integers: for `%`, `b ≠ 0 → 0 ≤ r < \|b\| ∧ ∃ q, a = q·b + r`; for wrap, the result is in range and congruent modulo `2^w`; for `/`, truncation and both abort cases; for shifts, the masked count. | Evaluated examples at every width's minimum, maximum, zero and −1. |
| `TH-CORE-01` | A | `validate m = ok → WellFormed m`, where `WellFormed` is the conjunction of specification §4.6's rules as propositions. | Modules with a forged root annotation, a summary missing a shrink, and a mistyped store are rejected. |
| `TH-MEM-01` | A | Growth preserves every valid location and its content: `StoreOk σ → Valid σ l → Valid (push σ o v) l ∧ read (push σ o v) l = read σ l`. | A reference taken before a push is read and written after it; an alias write changes the content while validity holds. |
| `TH-MEM-02` | A | The live-reference invariant — every reference or slice held by a variable in the demand set denotes a valid location of its type — is preserved by every `eval` step, including scope exit and, in `core-shrink`, every shrink that `V-SHRINK` admits. | A reference to a popped limited-array slot stays valid; a reference above a resizable's new length is invalid, and the program holding it live is rejected. |
| `TH-SAFE-01` | A | `validate m = ok → ∀ n p k, eval n p m ≠ fault k`. | The corpus's allocating, aliasing and recursive programs validate. For each rule of §4.6, a program violating only that rule faults at some fuel. |
| `TH-EXIT-01` | A, `core-construction` | A `return … from` with target `t` is caught by the nearest activation on the call stack whose implementation is in `t`; every scope between is removed; the store restricted to roots outside those scopes is unchanged except by the returned value's construction. | Recursive target (the §1 probe); two nested targets; a target that is not active is rejected by validation. |
| `TH-CON-01` | B, `core-construction` | The construction trace of a validated program satisfies `C-ONCE`, `C-DIRECT`, `C-RELOCATE`, `C-STAGE`, `C-NAMED` and `C-ABANDON`. | One program per rule whose mutated lowering violates it. |

`TH-SAFE-01` is proved by induction on fuel over the interpreter with `TH-MEM-02`'s invariant. It is conditional on nothing but validation; finite storage is modeled as unbounded, and exhaustion is `assumed` in the trust ledger.

### 4.2 Sharing and reuse

| ID | Tier | Statement |
|---|---|---|
| `TH-ERASE-01` | A | `eval` does not depend on contexts: replacing a module's context table changes no result. Root annotations, and with them root class, depth and writability provenance, are the erased distinctions. |
| `TH-SHARE-01` | A | Let `q` map implementations of `m` to implementations of `m'`. If `rename q (impl m f) = impl m' (q f)` for every `f`, globals agree and `entry m' = q (entry m)`, then `eval n p m = eval n p m'` for every `n` and `p`. |
| `TH-SHARE-02` | A | With `TH-SAFE-01`: if every context of `m` validates and `m'` is a quotient of `m` as above, `m'` never faults. Separately validated contexts may execute one shared body. |
| `TH-SHARE-03` | B | If a fact certificate is valid for `impl m' (q f)`, every `array.index.proven` in it is safe in every context mapped to it. |
| `TH-REUSE-01` | A | For a stage with key function `key` and result function `run`: if `key i = key j → run i = run j`, and every cache entry `(k, a)` satisfies `∃ i, key i = k ∧ run i = a`, then a cached run returns `run i` and leaves the cache satisfying the same invariant. The composition of such stages has the same property. |

`TH-SHARE-01` is the quotient of a function table. Its premise is the decidable check of specification §16.2: given a proposed partition, verify congruence. Nothing is concluded from printed bodies or types looking alike; the premise compares the bodies the interpreter executes, with callees mapped. The proof is by induction on fuel, which covers recursive groups without a separate argument.

Retained distinctions, which the premise forces to be equal: types and layouts, parameter modes and physical forms, the capture list, callees, the destination request, nonlocal target sets, and every check an operation performs.

Witnesses and counterexamples, each a Lean example and a source fixture:

| Case | Expectation |
|---|---|
| A function called with a global-rooted and a local-rooted slice | Quotient exists; both contexts validate; results equal. |
| A free variable bound to two different outer locals | Quotient exists. |
| Two contexts whose bodies differ in one retained bounds check | The congruence check fails; no quotient is claimed. |
| A body that reads the first parameter's length, shrinks through the second, then indexes the first; one context passes two arrays, the other passes one array twice | With the check kept, the bodies are equal and shared. A variant that removes the check on the strength of "the parameters name different arrays" is run under the second context and faults: a fact true in one context is not evidence for a shared body. |
| A result requested as a value and as an element run | Different bodies; no quotient. |
| A pool-form parameter and a plain resizable reference | Different signatures; no quotient. |
| A mutually recursive pair under two root contexts | Quotient exists. |

`TH-REUSE-01`'s first hypothesis — the key determines the result — is the completeness of dependency tracking. The theorem does not establish it and must not be cited as if it did. It shows only that nothing else is needed: cache consistency, build order and interleaving cannot break agreement with recomputation. The hypothesis is established per boundary:

| Boundary | How `key` determines `run` is established | Level |
|---|---|---|
| Native object | By construction: the key is the unit's whole text, the headers read and the contract. Residual assumption: the C compiler is deterministic. | `assumed`, tested by §10's verification mode |
| Whole build | By construction through the recording reader, which makes an unrecorded read fail in the test suite. | `differential-tested` |
| Checked result | Not established. Dependency sets are recorded and their prediction is tested (§10.3); no reuse depends on them. | `deferred` |

### 4.3 GIR

| ID | Tier | Statement |
|---|---|---|
| `TH-GIR-01` | A | The Lean GIR-H validator's acceptance implies the invariants it names: typing, dominance, scope balance, summary closure. It does not imply reference lifetime. |
| `TH-LOWER-01` | A, `core-pilot` | For the Lean lowering: `eval n p m = done o t → ∃ k, run k p (lower m) = done o t`. |
| `TH-LOWER-02` | B | The converse with a fuel bound, giving that a diverging Core program's lowering does not terminate. |
| `TH-BCE-01` | A | Each rule of specification §10 is sound, and a function whose fact certificate checks never fails an `array.index.proven`: replacing each by `array.index.checked` gives the same `run`. |
| `TH-CERT-01` | A | The executable certificate checker accepts only certificates satisfying `TH-BCE-01`'s premise for the module it is given. |
| `TH-LOW-01` | B | GIR-H to GIR-L lowering preserves `run` for `core-pilot` given a valid stack plan. |

The C++ lowering and the C++ verifier are `differential-tested`. Where the Lean tool validates and runs the GIR the C++ compiler exported and compares it with Core, that program's translation is `instance-checked`.

### 4.4 Review standard

Each Tier A theorem is read by a reviewer lane that did not write it, against six questions: can an interesting real program satisfy the assumptions; is the conclusion hidden in a predicate; does each summary follow from a body; are acceptance, final values, identity, aborts and construction cost confused; does it concern the model or the production algorithm; could a changed instance, notation or opaque definition alter the statement. The reviewer's answers go in `coverage.json` with the theorem.

## 5. Observation policy

| Profile | Compared |
|---|---|
| Release | Exact standard output; exit status; for an abort, its kind and source line. |
| Debug, unoptimized | As release, including overflow and cast aborts. |
| Debug, optimized | Mandatory aborts and release-visible results exactly; overflow aborts may differ where the optimizer regrouped or removed the operation. |
| Construction | The construction trace against specification §7.1's rules, not against native instruction counts. |

A timeout, a killed process, a truncated log, a missing backend or an unsupported feature is never a pass. Outcomes are `agree`, `mismatch`, `unsupported`, `harness-failure`, `inconclusive`. A mismatch is stored with its seed, source and commands.

## 6. Semantic fixture matrix

Each row is a family: a positive case, a boundary case, and a case that a wrong implementation fails. Fixtures live in `test/semantics/` as ordinary runnable fixtures with expected output, so the existing runner also checks them on the legacy pipeline in every configuration.

| ID | Profile | Scenario | Observation |
|---|---|---|---|
| `NUM-01` | pilot | Every width and sign at add, subtract, multiply boundaries | Wrap, or debug abort. |
| `NUM-02` | pilot | Zero divisor in a used and an unused expression | Abort in both; earlier effects kept. |
| `NUM-03` | pilot | `i64.min / -1` and narrower minimum over −1 | Abort always; debug abort or release wrap. |
| `NUM-04` | pilot | Euclidean remainder with negative operands, `min % -1` | Nonnegative; zero. |
| `NUM-05` | pilot | Shift counts −1, 0, `w−1`, `w`, `w+1` | Masked. |
| `NUM-06` | pilot | `as` and `as!` narrowing, widening, sign change | Debug range abort only for `as`. |
| `ORD-01` | pilot | Index expression grows the indexed array | Checked against the sampled length. |
| `ORD-02` | pilot | Index expression rebinds the slice variable being indexed | The original run is indexed. |
| `ORD-03` | pilot | By-value argument then an alias write; reference argument then a write | Snapshot; current content. |
| `ORD-04` | pilot | Compound assignment whose right side writes the target | Old value read first. |
| `ORD-05` | pilot | Short-circuit right side that aborts or writes | Not evaluated when skipped. |
| `ORD-06` | pilot | Range loop versus array loop while the array grows | Bounds once; length reread. |
| `MEM-01` | pilot | Reference kept across repeated pushes | Same element. |
| `MEM-02` | pilot | A callee writes an element the caller holds a reference to | Reference valid; value changed. |
| `MEM-03` | pilot | Reference to an inner-scope variable stored in an outer one; returned local reference | Rejected by the frontend and by `validate`. |
| `MEM-04` | shrink | Shrink with a live slice; last use before the shrink | Rejected; accepted. |
| `MEM-05` | shrink | Callee that shrinks its reference parameter while the caller holds a view | Rejected through the summary. |
| `MEM-06` | shrink | Limited array: pop, read through a kept reference, push | Valid read of the old then the new value. |
| `MEM-07` | shrink | Capacity overflow; pop on empty; negative resize | Abort before any change. |
| `STR-01` | shrink, flat structs | Construct a scalar-field struct local; mutate and print fields of a `let` owner | Core export, Lean Core, GIR-H and native GIR agree; independent field binding/contents permissions hold. |
| `STR-02` | shrink, flat structs | Copy a local struct, then change one field of the original | The copy retains its earlier field values; sibling fields of the original are unchanged. |
| `STR-03` | shrink, flat structs | Substitute a distinct nominal struct with identical fields/layout in a constructor or store | Rejected by Core `V-TYPE` and GIR `GIR-V010`, independent of the frontend. |
| `STR-04` | shrink, flat structs | Wrong constructor count/type, field index outside the descriptor, store to a `let` field, or write inside a `const` field | Count/type/selector failures reach typing checks; permission failures reach `V-MUT` or `GIR-V030`. Invalid wire table indices/arity fail decoding first. |
| `STR-05` | shrink, flat structs | Packed `u8` followed by `i64` at byte offset 1; read and write the latter | Source layout metadata is retained; native output matches Lean; generated scalar accesses pass alignment sanitization. |
| `STR-06` | shrink, flat structs | Existing pilot artifacts, a struct tag/table under `core-pilot`, and a missing/extra struct table under `core-shrink` | Pilot bytes and module arity unchanged; wrong profile-selected shape/tag rejected as malformed. Compare GIR pilot bytes at the same `gir-h/0.3` schema revision. |
| `STR-07` | shrink, flat structs | Whole-object `const` struct qualification or field projection from a temporary in the first slice | Explicit `unsupported: struct-whole-const` or `unsupported: struct-temporary-projection`; no partial artifact is published. |
| `STR-08` | shrink, flat structs | Scalar field initializers with output or an abort in the middle, including checked default initializers | Field order and one evaluation each; abort keeps preceding output and skips later initializers. |
| `CON-01` | construction | Nested call and branch constructing into a `push` destination | `C-DIRECT`, `C-ONCE`. |
| `CON-03` | construction | Limited receiver of an unknown-length result that fits and that does not | `C-STAGE`; abort with nothing written outside. |
| `CON-04` | construction | Constructor growing its destination array; growing another array | Rejected; accepted. |
| `CON-05` | construction | Pushed fixed element whose expression pushes to the same array | Accepted; evaluated before the push. |
| `CON-06` | construction | Whole assignment whose right side names the array, directly and through a callee | Rejected. |
| `CON-07` | construction | One returned local; two returned locals | No event; one copy. |
| `CON-08` | construction | `append` of several elements with a nonlocal exit during the third | Two published; the third abandoned. |
| `EXIT-01` | pilot | Fallthrough, `break`, `continue`, `return` from nested scopes | Scopes removed in order. |
| `EXIT-02` | construction | Nonlocal return across two intermediate calls with open scopes | Result delivered; intermediate roots gone. |
| `EXIT-03` | construction | Recursive target | The innermost active activation returns; outer ones resume. |
| `EXIT-04` | construction | Nonfixed result returned nonlocally into the target's destination | Result intact after intermediate watermarks restore. |
| `EXIT-05` | pilot | Abort inside nested scopes | Program ends; no further output. |
| `SHR-xx` | legacy backend, any feature | Specification §16.4, one member of the synthetic family per row | Asserted share or distinct. |

Generated corpus: the existing lanes of `fuzz/driver.py`, extended with the Lean tool and the `gir` pipeline as additional stages. `scalar`, `numeric`, `order` and the pilot-compatible `trap` kinds belong to `core-pilot`; `resize`, `reference` and the remaining `trap` kinds to `core-shrink`. No new generator is written.

`STR-01`–`STR-08` qualify the first flat-struct slice defined by [the struct encoding contract](goose-ir-spec.md#124-flat-fixed-structs-in-goose-core02-core-shrink) and [its GIR-H lowering](goose-ir-spec.md#125-flat-fixed-structs-in-gir-h03-core-shrink). They are planned checks, not results. The first end-to-end fixture is:

```goose
struct Packed { tag: u8, value: i64, const stamp: i16 }

fn main() {
    let p = Packed { tag: 1, value: 40, stamp: 7 };
    p.value += 2;
    print(p.tag, " ", p.value, " ", p.stamp);
}
```

Expected output is `1 42 7\n` in both numeric profiles. Check this fixture through source export, Lean Core validation/evaluation, GIR-H validation/evaluation, and GIR-L/native execution; compare it with the legacy backend. Run alignment sanitization on its generated C. Add separate minimal malformed/permission cases for `STR-03`, `STR-04` and `STR-06` so their failure reaches the intended layer. Flat structs alone satisfy none of `MEM-04`–`MEM-07` and do not reach `G-SHRINK`.

A disagreement between the Lean model and the legacy compiler is resolved by the campaign's decision O2 and recorded in `semantics/decisions.md` with a minimized reproducer. Expected outputs are never regenerated to resolve one.

## 7. Verifier and malformed-artifact matrix

C++ verifier cases are in-memory modules in `test/compiler_gir.cpp`. Decoder cases are files fed to `goose-semantics`; `test/semantics/malformed/check.sh` also generates the over-limit input so the repository does not carry a 64 MiB fixture.

| ID | Mutation | Layer | Evidence and status |
|---|---|---|---|
| `VER-01` | Unknown tag, wrong arity, wrong schema string, wrong profile | Decoder | Core and GIR malformed indexes; checked by the decoder scripts. |
| `VER-02` | Use not dominated by its definition; wrong edge argument type; two terminators | Verifier | In-memory C++ cases and GIR invalid fixtures assert `GIR-V020`. |
| `VER-03` | Store through `const`; slot address outside its scope; load of a resizable | Verifier | In-memory C++ cases and GIR invalid fixtures assert `GIR-V030`. |
| `VER-04` | Summary omitting a shrink; `call` to a function that may propagate a target | Verifier, `validate` | Core `rejected_call_global_init_touches_later.json` checks `V-CALL`; the in-memory call case checks `GIR-V050`; shrink summary is gated on S8. |
| `VER-05` | Destination opened and neither published nor abandoned on one path; published twice | Verifier | Gated on S9, which adds destination construction operations. |
| `VER-06` | Escape edge that leaves a scope entered; target not handled by a member | Verifier | Gated on S9, which adds construction and escape operations. |
| `VER-07` | Certificate fact not implied by a predecessor; proven index after a shrinking call; after a re-entered scope | Certificate checker | Parked until O1 adds the checker. |
| `VER-08` | Constant out of range; index out of table; trailing data; oversize input; excessive nesting | Decoder | Malformed indexes plus a generated 64 MiB + 1 input checked through both `validate` and `gir-validate`. |
| `VER-09` | Aborting operation with no origin | Verifier | In-memory C++ case and GIR invalid fixtures assert `GIR-V100`. |
| `VER-10` | GIR-H operation in a GIR-L module; two live resizables on one stack; watermark restored across a caller's destination | Verifier | Stage mixing and same-stack resizables assert `GIR-V090`; caller-destination restoration is gated on S9. |

Each implemented case fails at the named layer with the named diagnostic, not at an earlier unrelated one. Gated cases remain acceptance criteria for the milestone that adds their operations or checker.

## 8. Linter compatibility

Checked facts about the baseline: twelve shipped rules and a 65-id inventory (`docs/lint/rule-inventory.md`); three compiler warning ids (`src/typecheck.h:73-78`); process statuses 0 to 4 (`docs/lint/README.md:113-117`); facts are built after typecheck with no optimizer or backend (`src/main.cpp:1430-1443`); the facts header's `compiler_revision` is the runtime text hash (`src/lint_facts.h:420-421`).

| ID | Contract | Proof |
|---|---|---|
| `LINT-01` | Warning ids, text and consensus unchanged under ordinary commands and lint | `test/lint/run_tests.py`; the baseline suite's `// warning:` markers |
| `LINT-02` | The twelve rules and all inventory dispositions unchanged | `test/lint/run_tests.py` |
| `LINT-03` | `specialization_fanout` counts checked entry-reachable contexts under every pipeline and build mode | The synthetic family: fanout equals contexts while the cost report's implementations is smaller |
| `LINT-04` | Facts bytes for the lint fixtures and the linter's own source identical to the baseline compiler's, apart from `compiler_revision` when the runtime text changed | Byte comparison in `test/scale/parity.py` |
| `LINT-05` | Statuses, missing companion, protocol mismatch, offline imports unchanged | `test/lint/run_tests.py` |
| `LINT-06` | `check` and `lint` compute no stable keys, run no backend, need no Lean | `goose --check --build-report` shows zero keys computed and no backend phase; `test/lint/run_tests.py` passes with Lean absent from `PATH` |
| `LINT-07` | A units-built `goose-lint` gives the same results as the single-file one | `test/lint/run_tests.py --goose` against an install whose companion was built with `--units` |
| `LINT-08` | Facts scale case unchanged | `test/lint/facts_scale.py` |

A GIR-built companion is deferred: the linter's source uses features outside the three profiles.

## 9. Workloads

| Workload | Source | Use |
|---|---|---|
| Synthetic family | `test/scale/gen.py`, public, deterministic from its parameters | Every structural assertion; budgets; the edit matrix. |
| Compiler corpus | Existing fixtures, samples, the linter's source | Parity of default output; sharing and units correctness. |
| Aincrad3 | The local checkout, read-only, at a recorded commit, built in a scratch worktree | Attribution and edit-loop measurements. Only aggregate numbers enter this repository. |

If Aincrad3 is absent, every Aincrad3 row is recorded `unavailable` and no number is substituted.

Issue #9 reported 14,575 specializations and 66,026,053 bytes of C for an optimized Aincrad3 build, and a standalone emission median of 43.150 s. Those figures are historical, are emission-only, and are not a native compile, link or runtime measurement. They are a reason to measure, not a baseline: the campaign's first build item remeasures.

### 9.1 Synthetic family

Parameters: `M` shareable helper functions, each reached under `K` root contexts (globals and locals at several depths, writable and read-only), over `T` concrete element types, plus one instance of every must-stay-distinct row of specification §16.4 and one mutually recursive pair under two contexts. The generator states the expected counts for its parameters: checked contexts, entry-reachable contexts, and implementations after sharing.

Assertions, exact and not statistical:

- implementations after sharing equals the generator's expected count;
- every must-stay-distinct pair remains two implementations;
- `specialization_fanout` reports the checked contexts, unchanged by sharing;
- the program's output is identical with sharing on and off, in units and single-file mode.

The family also generates each edit of §10 as a deterministic source transformation, with the expected set of changed implementations.

### 9.2 Attribution checks

The cost report (specification §20) is checked for internal consistency: the per-function emitted bytes, helper, type, data and runtime bytes sum to the written output's size; contexts ≥ entry-reachable ≥ live ≥ implementations; phase times sum to the total within the unattributed remainder the report states. A report that fails these is not used.

## 10. Edit-based qualification

### 10.1 Matrix

Each row runs on the synthetic family and, where the edit can be expressed without altering its sources permanently, on Aincrad3 in a scratch worktree.

| ID | Edit | Expected locality |
|---|---|---|
| `E00` | Cold clean build | Everything. |
| `E01` | Warm no-op | Nothing runs: no frontend, no native compiler, no linker. |
| `E02` | Comment added above a function; blank line added | Frontend runs. No implementation digest changes. Only the module's locations unit recompiles. In a build with native debug information, that module's code units may also change; the report says which. |
| `E03` | Body of a leaf that is not inlined | That declaration's implementations change; only their units, and the locations unit if lines moved, recompile. |
| `E04` | Body of an inlined helper | Exactly the implementations in the report's inline closure of the helper change. |
| `E05` | Signature of a function | It and its direct callers, and their inline closures. |
| `E06` | Field added to a struct | Implementations whose layout dependencies include the type. |
| `E07a` | A call site passes a local where it passed a global of the same type | A context is added or replaced; no implementation changes except the caller's. |
| `E07b` | A call site passes a pool where it passed a plain array | One new instance and the caller change. |
| `E07c` | A callee gains a shrink of its parameter | The callee changes; a caller holding a view is now rejected, with the diagnostic a clean build gives. |
| `E08` | A specialization request added, then removed | One instance appears in one unit and disappears; no existing symbol is renamed; units not holding it or its caller keep their objects. |
| `E09a` | An overload added that now wins at one call site | That caller changes. |
| `E09b` | An import changed to a module providing the same name | Dependents of the name change. |
| `E09c` | An embedded file's content changed | Its users change. |
| `E10` | Compiler binary, C compiler, C flags, numeric profile, `-D`, target, runtime text changed, one at a time | A new contract; every unit compiles; the other contract's store is untouched and still warm when switched back. |
| `E11` | Store deleted | As `E00`. |
| `E12` | One object truncated; one object with a flipped byte; a completion record removed | Detected, discarded, rebuilt, reported; the result equals a clean build. The flipped byte is detected in verification mode. |
| `E13` | Build killed during publish and during link | The next build completes and equals a clean build. |
| `E14` | Two builds of one program started together | Both succeed; the executable equals a clean build's behavior. |
| `E15` | An edit introducing a compile error; one introducing a new warning in a function whose units do not change | The error is reported and no executable is reported as built; the warning is printed. |
| `E16` | An edit and its exact revert | The final state equals the initial clean build. |

### 10.2 Recorded for every row

Frontend phases that ran; contexts checked; implementation digests changed; units whose text changed; native compiler invocations and units per invocation; objects reused and missed; whether the link ran; wall time, CPU time and peak resident memory of the compiler and of the largest native compiler process.

### 10.3 Equivalence

For every row the incremental result is compared with a clean build of the same sources under the same contract:

- compiler exit status and diagnostics, byte for byte;
- every unit's text, byte for byte — unit text is a deterministic function of the inputs, and that is a contract this design owns;
- the program's output, exit status and abort diagnostics on the workload's run inputs;
- objects and executables are **not** required to be byte-equal; they are compared only in verification mode, as evidence about the C compiler's determinism.

Verification mode (`--verify-reuse`) recompiles every reused object and compares, and recomputes after an R0 hit. It is on for the whole matrix.

Shadow invalidation: for every row, the set of contexts the dependency recorder predicts invalid contains every context whose recomputed result digest changed. The size of the over-approximation is reported; an under-approximation fails the row.

A randomized sequence of matrix edits, with a fixed seed, is run with verification mode on; any divergence from a clean build fails.

### 10.4 Structural acceptance

These gate regardless of host load, because they count events and not time.

| Gate | Requirement |
|---|---|
| `L-NOOP` | `E01`: zero native compiler processes, zero linker processes, zero frontend phases. |
| `L-LEAF` | `E03`: native compiler input is exactly the units holding an implementation of the edited declaration, plus at most one locations unit. |
| `L-LOC` | `E02` without native debug information: no code unit recompiles. |
| `L-ADD` | `E08`: no existing symbol renamed; no unit recompiled that holds neither the new instance nor its caller. |
| `L-SHARE` | §9.1's exact counts. |
| `L-EQ` | §10.3 for every row. |
| `L-FAIL` | `E11`–`E15` as stated. |

## 11. Budgets

Proposed values. They are frozen in the campaign's baseline section after the first quiet-host measurement and are then gating at the campaign's close; until then they are recorded, not enforced. Time is CPU time, minimum of at least five interleaved runs, taken only when `perf-gate-ready` exits 0 before and after. A regression counts only beyond the observed spread.

| Budget | Proposed |
|---|---|
| Report disabled | No measurable change in `--check` or emission CPU time against the baseline compiler. |
| Report enabled | At most 10% added CPU time. |
| `E01` | At most the larger of 1 s and 2% of `E00`'s wall time. |
| `E03` | Wall time minus frontend time at most 15% of `E00`'s native compile and link time. |
| `E00` in units mode | Wall time at most the single-file build's at the host's parallelism; CPU time at most 1.3 times. |
| Units-mode program runtime | Reported against single-file at the same C optimization level; more than 10% slower on a benchmark kernel requires a recorded tradeoff. |
| Compiler peak memory | At most 1.1 times the baseline's on the same workload. |
| Emitted bytes | Reported before and after sharing. Not a success criterion by itself. |

No speedup is claimed until measured. A reduction in emitted bytes with no reduction in a measured cost is reported as such.

## 12. Commands

Existing:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug && cmake --build build --parallel
python3 test/run_tests.py --profile baseline --cc native --require-clang
python3 test/lint/run_tests.py --goose build/goose
python3 test/lint/facts_scale.py --goose build/goose
python3 test/run_tests.py --goose-in-goose-only --exe build/goose --cc native
python3 fuzz/driver.py smoke --lane scalar --exe build/goose --cc clang
```

To be delivered by the campaign:

```sh
(cd semantics && lake build)
semantics/.lake/build/bin/goose-semantics audit
python3 test/semantics/run_tests.py --goose build/goose --profile core-pilot [--case NAME]
python3 fuzz/driver.py run --lane order --exe build/goose --cc clang --count 2000 --seed 1 \
    --semantics semantics/.lake/build/bin/goose-semantics --pipeline gir
python3 test/scale/parity.py --goose build/goose --baseline <baseline goose>
python3 test/scale/gen.py --contexts 64 --helpers 16 --types 4 --out <dir>
python3 test/scale/edit_matrix.py --goose build/goose --workload synthetic [--case E03]
python3 test/scale/edit_matrix.py --goose build/goose --workload aincrad3 --source <checkout>
```

Every harness exits nonzero on a mismatch, a malformed artifact or a required configuration that is missing, and prints a JSON summary with the outcome classes of §5.

## 13. Gates

| Gate | Evidence |
|---|---|
| `G-GROUND` | Baseline suite status recorded; loop commands timed on a quiet host; Lean audit command runs; Aincrad3 availability recorded. |
| `G-PILOT` | `TH-FUEL-01`, `TH-NUM-01`, `TH-CORE-01`, `TH-MEM-01`, `TH-MEM-02` and `TH-SAFE-01` for `core-pilot` pass the audit; pilot fixtures and lanes agree between the legacy compiler and Lean. |
| `G-ATTR` | Cost report passes §9.2 on the synthetic family and Aincrad3; growth is attributed to dimensions; budgets frozen. |
| `G-SHARE` | `L-SHARE`; `TH-ERASE-01`, `TH-SHARE-01`, `TH-SHARE-02` pass the audit; the full baseline suite passes with sharing on; default output byte-identical to the baseline. |
| `G-UNITS` | `L-NOOP`, `L-LEAF`, `L-LOC`, `L-ADD`, `L-EQ`, `L-FAIL`; `TH-REUSE-01` passes the audit; the full baseline suite passes in units mode. |
| `G-GIR` | Profile fixtures and lanes agree across legacy, Lean and `--pipeline gir`; §7 passes; `TH-GIR-01`, `TH-LOWER-01` pass the audit. |
| `G-SHRINK`, `G-CONSTRUCT` | The profile's fixtures, lanes and Tier A theorems. |
| `G-BCE` | `TH-BCE-01`, `TH-CERT-01`; `VER-07`; proven indexes on the pilot corpus are accepted by the Lean checker. |
| `G-CLOSE` | §8; §11's frozen budgets; the Aincrad3 edit-loop table; the claim ledger. |

## 14. Report template

```text
Gate, base and candidate revisions:
Environment (compiler, libc, kernel, architecture) and host load at measurement:
Profiles and features implemented:
Theorems passing the audit; theorems parked, with their proved lemmas:
Production connection (differential-tested / instance-checked) per feature:
Commands run; agree / mismatch / unsupported / harness-failure / inconclusive counts:
Cost attribution: counts table; top growth dimensions; sharing blockers:
Edit matrix: per row, the §10.2 record and the §10.3 result:
Aincrad3: available or unavailable; commit; the same tables, aggregates only:
Budgets: proposed, frozen, measured:
Disagreements with the legacy compiler and their resolution:
Deferred components: boundary, reason, prerequisite, acceptance condition:
```
