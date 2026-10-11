# Campaign: Goose Semantic Linter — Canonical Frontend, Goose-Native Rule Engine

**Primary design input:** [Issue #10 — RFC: A semantic linter for Goose](https://github.com/joshuarli/goose/issues/10)
**Target:** An unattended coding agent working in a local checkout
**Completion unit:** A working, tested, documented v1 lint command—not implementation of every speculative RFC rule.

> **Agent mandate:** Implement this campaign end to end, making conservative engineering decisions where the code differs from the audited baseline. Do not stop after scaffolding, a parser-only prototype, or a plan. Do not invent proofs or report incomplete analysis as clean. Keep the production compiler authoritative. Respect the repository's current `AGENTS.md`, including its no-push instruction. Preserve the existing language, program output, diagnostic text for existing commands, and bootstrap behavior unless a change is explicitly specified below.

---

## 1. Executive decision

**Build the linter primarily in Goose, not a second parser in Goose.** Retain Goose's existing C++ compiler as the one canonical lexer/parser/resolver/typechecker, and add a small, versioned semantic-facts bridge. Implement the rule engine, configuration, contract matching, suppression resolution, baseline management, classification, and rendering in `.goose` files. Expose the result through `goose lint` with a separately built, bundled Goose-native companion executable.

```
user .goose program + imports
         |
         v
production goose compiler (C++)
 parse -> resolve -> typecheck -> pre-optimization fact extraction
         |             \
         |              -> existing warnings with stable IDs
         v
validated, versioned lint-facts stream (local, private transport)
         |
         v
goose-lint, implemented in Goose
 fact model -> rules -> policies/contracts -> suppressions/baseline
         |
         v
goose lint: terminal text or JSON Lines + explicit coverage + exit status
```

### Why this architecture

1. The production compiler's AST, type resolution, reference roots, writability, effects, and call specialization facts are essential. Reimplementing or guessing them would create a semantically unreliable linter.
2. The repository has a Goose-written compiler under `test/goose_in_goose/`. **Do not use it as the linter's parser/typechecker.** Its README identifies it as a deliberately incomplete subset/bootstrap regression fixture, not a semantic source of truth. Preserve that fixture and use it as a regression/dogfooding workload instead.
3. The production frontend is written in C++ (`src/lexer.h`, `parser.h`, `ast.h`, `typecheck*.h`) and drives compilation through `src/main.cpp`. `TypeCheckProgram` precedes `Optimizer`; extracting facts at this boundary preserves the source shape.
4. Current `TypeCheck::Warn` / `PrintWarning` are string-based. They already delay and deduplicate warnings by original nodes and checks; this behavior must survive conversion to stable coded records.
5. AST `Line` presently identifies file and line, not universally precise token/end offsets. Accurate span capture is a real work package, not a field that already exists.
6. The existing CMake build produces `goose`; Goose-native programs can be built by the compiler, and `stdlib/os.goose` and `stdlib/json.goose` provide practical file, argv, stdout/stderr, and JSON functionality. A companion executable is simpler and safer than embedding a second runtime or writing a new C++ rules engine.

### Non-negotiable invariants

- No duplicate grammar, lexer, name resolver, or typechecker in linter code.
- No changes to whether valid Goose programs compile or how they run.
- No target-program execution, generated-C execution, or implicit native sidecar build during linting.
- No implicit network access while linting; optionally permit a clearly named explicit fetch mode.
- No heuristic finding may masquerade as a proof. Unknown facts must remain unknown.
- Default rules are precise; opt-in performance/review/project policies are clearly marked.
- Existing `goose run`, `goose build`, `goose check`, `--check`, `--multi-test`, existing `// warning:` fixtures, and the Goose-in-Goose bootstrap must retain their behavior.
- Release artifacts must work without the source checkout, external Python, or a second compiler installation.

---

## 2. Scope and definition of v1

Issue #10 contains **65 candidate rule IDs**: a mixture of existing compiler warnings, portable rules, review suggestions, and rules that require application contracts. Its catalog explicitly does **not** propose enabling everything by default. The campaign implements the following complete v1 product and assigns every other candidate an explicit deferred disposition.

### 2.1 Required v1 capabilities

- `goose lint <root.goose>` using the exact production compiler's import/typechecking semantics.
- `--format text|jsonl`, `--group <name>`, repeated `--deny <rule-id>`, repeated `--allow <rule-id>`, `--config <path>`, `--baseline <path>`, `--write-baseline`, `--require-complete`, `--allow-fetch`, `--help`.
- Machine-readable **existing compiler warnings** with stable codes, while preserving their original human text and deduplication under existing compiler commands.
- A versioned, validated source/semantic facts transport between the C++ frontend and Goose-native linter; no generated C needed for normal correctness rules.
- A Goose-authored registry of rules, severities, groups, confidence, contracts, suppression processing, baseline lifecycle, deterministic sorting, and output.
- Local, reasoned suppressions, stale/unknown suppression diagnostics, and exact-finding baselines (no file-wide exemptions).
- Honest source and specialization coverage, incomplete-analysis records, and explicit process exit statuses.
- A reproducible CMake build and packaging flow for the companion executable, working across supported platforms.
- Meaningful smoke and regression tests, including self-linting the linter's own Goose sources.

### 2.2 Required rules

| Rule ID | Group / default | v1 semantics and evidence requirement |
|---|---|---|
| `redundant_cast` | existing / same warning behavior | Reclassify the existing cast warning, preserving its existing specialization-dependent consensus semantics; do not implement a new cast proof. |
| `redundant_reference_marker` | existing / same warning behavior | Reclassify existing `&` warnings with resolved-call context; leave compiler warnings unaltered outside lint mode. |
| `avoidable_reference_copy` | existing / same warning behavior | Reclassify the existing copy warnings. Only recognize proven extra copies; never recommend borrowing where the lifetime rules require a value. |
| `discarded_failure` | correctness / warning for known contracts | Detect a known, resolved fallible function's status when it is discarded or provably overwritten without inspection. A generic bool is not an error contract. |
| `unchecked_poll_result` | correctness / warning | Recognize the exact `qpoll<T>()` builtin and its received-status result; handle scalar consumption of a multi-result call as well as unused status bindings. |
| `unused_pure_value` | suspicious / warning only for proven cases | Identify discarded value-producing expressions whose *complete evaluated subtree* is proved free of side effects, aborts, I/O, nonlocal control flow, mutation, and unknown calls. |
| `stale_suppression` | correctness / warning | Report unknown, malformed, unused or no-longer-matching local suppressions; baseline staleness has its own structured diagnostic. |
| `post_overflow_guard` | review / opt-in | Recognize a restricted typed signed-add/subtract-then-compare idiom that purports to detect overflow after it occurred. Show operands and debug/release distinction. |
| `stale_slice_length` | review / opt-in | Show a captured slice and later same-root growth where later behavior actually depends on the new extent; otherwise abstain or emit only an explicitly requested low-confidence hint. |
| `specialization_fanout` | performance / opt-in | Report actual source-function specialization counts for the selected entry/profile; show the contributor contexts, not a guessed runtime penalty. |
| `view_before_append_argument` | project / opt-in with contract | Require a declared owner/view/append/index contract and proven call evaluation order before reporting a frozen view used for a later index. |
| `foreign_container_index` | project / opt-in with contract | Require index provenance and consumer-owner metadata; only flag demonstrable owner mismatches. Raw integers or same numeric value prove nothing. |

**Rules are not delivered by merely registering an ID.** Each required rule needs positive fixtures, at least two legitimate counterexamples, contextual evidence, suppression tests, JSON/text snapshots, and a specialization/coverage test when applicable. If implementation discovers insufficient facts for an opt-in rule, extend the facts conservatively; do not silently convert the rule into name matching or a misleading warning. Restricted, evidence-backed subcases are acceptable only if the documented supported shapes and limitations are explicit and tested.

### 2.3 Explicitly deferred candidates

These issue #10 candidates remain documented future work, **not fake implementations or default diagnostics**. Maintain a machine-readable `docs/lint/rule-inventory.md` or equivalent with one row per ID, classification, rationale, missing fact/proof, and a testable promotion condition.

- **Results/flow:** `dead_store`, `unreachable_branch`, `duplicate_condition`, `self_assignment`, `ineffective_local_copy`, `discarded_error_variant`, `catch_all_hides_new_case`, `ignored_checked_helper`. Promote proven CFG/alias cases only after control-flow fact contracts are tested. The project error rules need declared domain contracts.
- **Numbers/bounds:** `narrowing_without_bound`, `checked_counter_without_guard`, `intermediate_width`, `signed_unsigned_boundary`, `bound_checked_after_use`, `off_by_one_range`, `lossy_float_contract`, `integer_division_rounding`, `masked_shift_count`, `remainder_contract`. Numeric invariants, short-circuit proofs, overflow profiles, and domain policies are distinct and must not be collapsed into text patterns.
- **References/values:** `shallow_const_write`, `mutable_read_parameter`, `composite_identity_equality`, `grow_during_iteration`, `copy_amplification`. Some legal Goose patterns are intentional; distinguish advisory findings from violations.
- **Pools/storage:** `unversioned_reusable_identity`, `free_then_reuse_identity`, `escaped_scratch_retention`, `loop_storage_accumulation`, `unbounded_optional_cache`, `raw_memory_persistence`. Logical identity and optional caching need ownership/project metadata; stack reports are not evidence of resident-memory cost.
- **Build/performance:** `large_emitted_function_family`, `runtime_dispatch_reaches_all`, `repeated_linear_lookup`, `quadratic_accumulation`, `bytewise_buffer_work`, `slow_io_in_loop`, `large_value_parameter`. Require emitted-size or measured evidence before optimization claims.
- **FFI/concurrency:** `ffi_signature_contract`, `ffi_result_ignored`, `unchecked_external_length`, `unstable_package_identity`, `unsafe_measurement_flag`, `worker_global_copy`, `worker_abandoned_at_main_exit`, `blocking_queue_cycle`, `resource_handle_lifecycle`. Do not infer C semantics from Goose name spelling alone.
- **Application/maintainability:** `truth_crosses_subjective_boundary`, `nondeterministic_causal_input`, `partial_update_before_refusal`, `default_overwrites_explicit`, `sentinel_crosses_domain`, `public_api_inferred_contract`, `unused_definition`, `readability_hotspot`. These require explicit entry, module, transaction, causal, or style contracts.

**No candidate may disappear:** the completed inventory must contain all 65 unique IDs from issue #10 exactly once, with 12 required v1 and 53 deferred. Generate/validate this count in the campaign tests or release checklist. A deferred row is not a product feature.

### 2.4 Out of scope

Do not build a general dataflow theorem prover, second optimizer, reflection runtime, separate parser, live language server, SARIF exporter, general autofixer, incremental daemon, application-specific Aincrad3 integration, code formatter, language syntax extension, or blanket style linter. The native C++ compiler is not being rewritten in Goose. Those are separate reviewed projects.

---

## 3. Architecture and responsibility boundaries

### 3.1 Production frontend (C++, authoritative)

Create a narrow diagnostic/facts extraction layer invoked **after successful `TypeCheckProgram` and before `Optimizer`**. Use stable original source nodes (`Node::Origin`) to relate typechecked clones and specializations to source constructs. Do not scrape compiler stdout, generated C, `--dump`, or `--specs` to reconstruct semantics.

Recommended files (adjust exact filenames after inspecting current tree):

```
src/lint_diagnostics.h        # typed warning codes, canonical emitter/sink
src/lint_spans.h              # parser-side source token/span mapping
src/lint_facts.h              # deterministic typed-fact traversal/serialization
src/lint_driver.h             # lint verb, transport files, child launch, status
src/main.cpp                  # minimal CLI/pipeline hooks
src/ast.h / src/parser.h      # minimal span/source metadata, where needed
src/typecheck*.h             # coded existing warning sites, minimal fact hooks
```

Responsibilities: exact parsing/imports/typechecking, source identity, resolved callee identity, type and result arity, clone/origin relationships, reference/copy/alias facts that already exist, trustworthy effect/provenance signals, specialization context, coverage, and diagnostic capture.

**Do not** place individual lint-policy engines into `typecheck*.h` or give a `Warn` call a guessed rule ID based on its message text. Match existing warning sites to explicit stable enums/constants. Avoid changing checker control flow just to satisfy lint output.

### 3.2 Goose-native lint engine (policy and analysis)

Recommended modules:

```
tools/lint/main.goose         # entry / command arguments / lifecycle
tools/lint/facts.goose        # versioned JSONL decoder, validation, fact tables
tools/lint/model.goose        # typed lint value model, indexed graph, spans
tools/lint/rules.goose        # registry and rule scheduling
 tools/lint/rules_results.goose
 tools/lint/rules_values.goose
 tools/lint/rules_review.goose
 tools/lint/rules_contracts.goose
tools/lint/contracts.goose    # exact API and owner/result contract matching
tools/lint/policy.goose       # config, group selection, severity override
tools/lint/suppress.goose     # local suppression semantics + staleness
tools/lint/baseline.goose     # stable fingerprints + lifecycle
tools/lint/output.goose       # deterministic text/JSON Lines writer
tools/lint/README.md         # implementation, build, dogfooding notes
```

Use concise, descriptive Goose modules and existing stdlib JSON and OS interfaces. The compiler's own rule engine must compile with unmodified language semantics, pass ordinary typechecking, and lint itself. Do not depend on Python in the delivered executable.

Goose implements **rule decisions, evidence assembly, confidence classification, deduplication, policies and reporting**, not just an output formatter. `src/` may compute semantically necessary primitive facts; it must not quietly implement the entire lint ruleset instead.

### 3.3 CLI and packaging

Provide a working **`goose lint`** driver verb. The driver writes a securely created, bounded, temporary facts stream, invokes a bundled `goose-lint` native executable with argument vectors (never shell interpolation), consumes the result, and removes temporary files on all successful and failed paths.

`src/process.h` currently exposes `RunProcess` that combines child stdout and stderr. To guarantee clean JSON Lines even on a child failure, make the companion write its final output to a **separate temporary output file**; capture process noise for error reporting only. This avoids depending on the current combined-stream API's behavior. Use platform-safe temp paths, atomic creation, restrictive permissions, explicit size/resource limits, and cleanup guards. Never let filenames or source code become shell fragments.

CMake should provide an **`goose-lint` build target** depending on the built compiler, compiling the Goose modules to a standalone native executable. An ordinary supported distribution build/install must include the companion adjacent to `goose` (or at a well-defined packaged relative resource path), plus smoke tests from a relocated installation. Avoid dependency cycles: build the C++ compiler first, then compile the Goose companion with that compiler. Do not require the Goose sources at runtime.

If the companion is missing or incompatible, `goose lint` must fail with a clear actionable tool error; it must not produce an empty success. Embed/print protocol versions in both sides and check them before analysis. The `goose lint --help` path must work without parsing a source file and explain shipped/opt-in rules, output formats and status codes.

### 3.4 Offline and side effects

A standard lint run must not execute target code, generate/compile its C backend, launch source-defined native sidecars, fetch packages, or mutate project files. The current import path may fetch/build dependencies as part of ordinary compiler workflows; implement a lint-specific offline guard at the canonical package resolution boundary. Use already installed/available imports, and fail with explicit missing-dependency diagnostic if a required package cannot be resolved offline. `--allow-fetch` permits a documented package-fetch path but **not** target program execution or arbitrary sidecar commands. Do not silently skip imports and analyze a different program.

Existing in-process frontend activities necessary for checking a program (for example validated embedded shader processing, if encountered) must be inventoried. If they cannot safely run in lint mode without side effects, produce an explicit unsupported/input error with coverage; do not claim they were typechecked when they were not.

---

## 4. Data contracts

### 4.1 Semantic facts transport (private, versioned)

Use UTF-8 **JSON Lines** with a strict first `header` record, typed fact records, `coverage` records, and exactly one terminal `end` record. JSONL avoids needing a single massive nested JSON document and provides low-cost field-level fixtures. Version this internal bridge independently from public lint diagnostics (`facts_version: 1`); it may evolve in lockstep with the bundled companion, but mismatches must fail closed.

**Illustrative shape** (field names may be normalized after implementation; avoid exposing raw C++ pointers, addresses or unstable enum integers):

```json
{"kind":"header","facts_version":1,"compiler":"goose","revision":"<build-id>","entry":"app.goose","profile":"O1"}
{"kind":"source","file_id":0,"path":"app.goose","content_hash":"<hash>","line_endings":"lf"}
{"kind":"node","id":37,"origin_id":19,"specialization_id":4,"node_kind":"call","source":{"file_id":0,"start_byte":80,"end_byte":97,"precision":"exact"},"type_id":12,"result_arity":2,"resolved_callee_id":8}
{"kind":"result_use","call_node_id":37,"result_index":1,"state":"discarded","evidence":"scalar-use-of-multi-result"}
{"kind":"coverage","file_id":0,"parse":"complete","check":"partial","unchecked_generics":2,"reason":"not instantiated by selected entry"}
{"kind":"end","record_count":5,"integrity":"<checksum>"}
```

Actual implementation must define and test a complete `docs/lint/facts-v1.md` schema with: required/optional keys, enums, referential integrity, version mismatch, duplicate IDs, size limits, corruption/EOF detection, source mapping, source hash, entry set, chosen frontend/profile options, flags that affect typed semantics, status/error records, and deterministic ordering.

Export only the facts rules actually consume; do not serialize the entire mutable `Ast` or compiler internals. Initial minimum:

- **Source/locations:** normalized source path, original buffer identity, byte offsets (0-based, half-open), line/column conversion, lexical comment/suppression spans, original-node ID. Do not expose absolute host directories unnecessarily in portable output.
- **Typed nodes:** expression/statement kind, parent/children, original node relation, enclosing statement/function, resolved type and signed width where applicable, constant/proven range where available, explicit/implicit copy/reference adaptation.
- **Calls/results:** fully resolved package/module-qualified callee and overload identity, exact builtin IDs, result count and types, target binding(s), scalar versus tuple consumption, reads/overwrites of status outputs when proven.
- **Effects:** conservative lattice including `pure`, `reads`, `writes`, `I/O`, `may_abort`, `nonlocal_exit`, `unknown`. Distinguish a **proven empty observable effect set** from `unknown`; a misleading `pure=true` default is forbidden. Include transitive calls, construction defaults, bounds checks and possible runtime traps where relevant.
- **Roots/views:** compiler-known root/provenance and writability, alias certainty (`same`, `disjoint`, `may_alias`, `unknown`), slice capture length semantics, growth/append operations, and the exact call evaluation order when used by a rule.
- **Specializations:** stable description of checked entry, source function, concrete type/root/function/destination context, and source-to-clone mapping, without pointer-based public IDs.
- **Coverage:** parsed files, reachable/checked specializations, uninstantiated generic bodies, unsupported analyses and skipped facts with reasons.

**Stable identity:** Allocate fact IDs deterministically from canonical source traversal and sorted specialization descriptions; pointer addresses may be used as temporary lookup keys *within one compiler run* but never serialized as user-facing identifiers. Never use a specialization's incidental hash-table traversal order as an ordering contract.

### 4.2 Source locations and comments

The current AST `Line` is a file+line pair. Extend the canonical lexer/parser with a small side table of original-node `SourceSpan`s rather than changing every `Node` constructor solely for lint. Capture token starts and construct ends as the parser reads original source; cloned nodes map via `Origin()`. Keep source buffers alive; index newline boundaries once per file. Handle tabs, UTF-8, CRLF, multiline raw strings, nested syntax, generated implicit nodes, and imports.

Public diagnostic locations are 0-based UTF-8 byte offsets with optional human 1-based line/column. LSP UTF-16 conversion is **not** part of v1. For existing warnings without a legitimate exact span, encode `precision:"line"` and nullable columns/offsets. Never fabricate end columns from a generic `Line`. All new required rule findings must have testable primary spans for their supported source constructs.

Capture comments only as source metadata: no new Goose syntax. Keep malformed parser fixtures untouched. Suppression markers are recognized only in lexer-known comments, never in strings or raw-string literals.

### 4.3 Existing warning compatibility

Assign stable codes at their existing emission sites, then route them through a typed `DiagnosticSink`. Keep `Warn`'s deferral, loop/join retry, `quiet` logic, redundant cast consensus, and original-node warning dedup semantics intact. Ensure existing commands still print the **same warnings with the same text, multiplicity and ordering**, unless a separately documented additive `--diagnostic-format` option is chosen; the lint verb alone changes formatting.

Never infer rule codes through regexes over message text. If multiple warnings genuinely share a source node, preserve both when evidence/rule differs. If different specializations disagree on redundancy, honor the existing compiler proof policy, not a union of convenient per-clone guesses.

### 4.4 Public diagnostic schema v1

Define `docs/lint/diagnostics-v1.md`. The public `--format jsonl` stream contains a `header`, 0+ `diagnostic` records, explicit `coverage` record(s), and `summary`, with `schema_version:1` and deterministic ordering. Example:

```json
{"kind":"diagnostic","schema_version":1,"code":"discarded_failure","group":"correctness","severity":"warning","confidence":"high","message":"parse_int success result is discarded","primary":{"path":"src/app.goose","start_byte":120,"end_byte":141,"precision":"exact"},"related":[],"evidence":{"callee":"std::parse_int","status_result":1,"use":"discarded"},"specializations":[],"suppression":null,"suggestion":"Inspect or explicitly justify the parse failure path","fixable":false}
```

Specify exact required keys, consistent nullability, JSON escaping, and backward-compatibility policy. Stable codes and schema semantics are compatibility commitments; cosmetic messages, suggestion wording, and internal fact IDs are not. Avoid embedding compiler memory pointers or process-specific temp paths in public output. Source paths are project-root-relative where possible and stable across working directories.

Sorting: normalized project-relative path, primary start byte, rule ID, normalized evidence key, specialization context. Deduplication: origin node + rule + relevant evidence + applicable specialization context, **not** source line alone and not arbitrary pointer. Preserve divergent specialization outcomes; include context or an aggregate only when all applicable specializations satisfy the same proof.

### 4.5 Coverage is part of the answer

A program may typecheck only specializations reachable from the selected root; unused generic/exported code need not be semantically checked. Report parsed-source coverage separately from checked-semantic coverage. Provide the selected entry set, number of reached specializations, skipped uninstantiated bodies, and any analysis limitations. `--require-complete` fails if declared required entries or configured mandatory analyses are not covered. Failure to read facts, resolve an import, or run the Goose companion is a tool/input error, never `0 findings`.

Expected unknown at an individual use site means **abstain with a reason/counter**, not a manufactured proof. Mandatory fact-producer or protocol failures must terminate unsuccessfully. Do not interpret absence of warnings as soundness over uninstantiated code.

---

## 5. User-facing interface and policy

### 5.1 CLI examples and exact behavior

```sh
goose lint app.goose
goose lint app.goose --format jsonl
goose lint app.goose --deny discarded_failure
goose lint app.goose --group performance
goose lint app.goose --config goose.lint.json --baseline .goose-lint-baseline.json
goose lint app.goose --require-complete
goose lint app.goose --allow-fetch
```

Retain `goose check` as a compiler command, distinct from the lint policy/deny status. No compiler error may be downgraded by `--allow`. CLI overrides configuration for severity/rule selection; local suppressions only affect lint findings, never source/compiler errors. Invalid rule IDs or incompatible options are configuration errors. A `--group` selection must use documented group semantics and not silently add all exploratory rules.

| Exit | Meaning |
|---|---|
| `0` | Completed requested analysis; no unsuppressed finding selected as denied. Ordinary warnings may be present. |
| `1` | Completed requested analysis, with one or more denied findings. |
| `2` | Invalid Goose program or required source/import input failure; this is not a successful lint. |
| `3` | Invalid lint config, contract, baseline, suppression policy or CLI argument. |
| `4` | Internal tool, companion, facts/protocol, or mandatory analysis failure. |

Errors must retain a machine-readable form in JSONL mode. Do not print `parsed ok` / `typechecked ok` or child startup logs into the JSONL stream. Non-JSON diagnostics and debug logs may go to stderr only in text mode or as deliberately non-protocol output on explicit verbose settings. No empty-success fallback.

### 5.2 Configuration

Use JSON so the implementation can use existing Goose stdlib functionality. Proposed `goose.lint.json`:

```json
{
  "schema_version": 1,
  "default_groups": ["correctness", "suspicious"],
  "enable": ["unchecked_poll_result"],
  "deny": ["discarded_failure"],
  "allow": [],
  "review": {"specialization_fanout": {"min_count": 30}},
  "contracts": "goose.lint-contracts.json",
  "baseline": ".goose-lint-baseline.json"
}
```

Document actual defaults; above is illustrative. Do **not** set a universally justified specialization count of 30; performance thresholds are user-selected review/report policy and reflect workload needs. Reject unknown fields/IDs by default and include actionable paths/keys. Version config separately from the facts and public diagnostics.

Define exact **resolved callee identifiers**, not substrings such as `parse`, `checked`, `error`, `bool`, or `push`. Seed the documented core fallible API contracts, including the actual `std::parse_int` result convention and `qpoll`. Use explicit library manifests/API identity for third-party and project functions, with signature/revision binding to detect contract drift.

### 5.3 Suppressions

No language change. Define one precise source-comment syntax, e.g.:

```goose
let n, ok = parse_int(trusted_text);  // goose-lint: allow[discarded_failure] -- validated upstream
```

Allow a directive on the finding statement's line or on the immediately preceding comment line; bind it to the **single nearest following statement** only when unambiguous. A directive never implicitly disables a rule for a whole file/function. Require a nonempty reason. Record the matched finding ID and reason in diagnostics/coverage. Reject malformed/unknown IDs; report unmatched/stale directives under `stale_suppression`. A suppression only applies to a result with the same original source and rule, not to unrelated specializations or new findings elsewhere. Do not alter regular `// warning:` test assertions or parse inside raw strings.

### 5.4 Baselines

A baseline is for controlled adoption, not permanent invisibility. Give each finding a fingerprint based on rule, normalized project-relative path, source construct/context, resolved callee/contract evidence, and collision-disambiguating local occurrence—not just line number or arbitrary compiler ID. Serialize the fingerprint algorithm/version. Do not promise stability under all semantic refactors. Sort and write atomically; never rewrite baseline during a normal lint.

`--write-baseline` is an explicit mutating action, covered by tests for duplicate/stale/conflicting entries and source drift. A matched baseline finding is recorded as suppressed/baselined, not deleted from machine-readable results. Stale baseline entries are reported and selected policy may deny them; broad wildcard file baselines are forbidden.

### 5.5 Suggestions and fixes

A suggestion explains the precise diagnosed risk; it is **not** an edit guarantee. Do not implement automatic fixes in v1. `--fix` should be rejected as unsupported rather than silently doing nothing. Future fix support must require a compiler-backed equivalence proof, conflict-free source edits, re-typechecking and behavior equivalence in both debug/release profiles. Overflow rewrites, borrow/copy changes, cache insertion, and contract changes remain human-reviewed proposals.

---

## 6. Detailed rule proof obligations

### 6.1 `discarded_failure` / `unchecked_poll_result`

Use resolved identities and result positions. The compiler already knows multi-result calls and binding modes; export those as facts. Build a bounded per-function def/use graph in Goose to distinguish: discarded trailing result, result destructured but never read, success status overwritten before inspection, status propagated outward, assertion/guard consumption, and unknown aliases/closure capture. A call whose success output flows into a meaningful return/branch is **not** discarded.

Start with exact builtin `qpoll` status and documented standard-library fallible functions; add application APIs only through contracts. A generic boolean-returning function, an intentionally ignored non-failure bool, a returned status, a checked status, an explicitly reasoned suppression, and an unknown escape must all be non-finding cases. `qpoll`'s zero-valued result on miss makes blindly using only the first result suspicious, but the tool must not allege a runtime failure actually occurred.

**Acceptance:** golden fixtures cover all result-use forms, interprocedural resolved API identity, overloads, tuple/scalar contexts, multiple specializations, and suppressions; no name-only or bool-only false positives.

### 6.2 `unused_pure_value`

A discarded expression is eligible only when all evaluated subexpressions are proven non-observable under the actual debug/release rules. Model short-circuit order, implicit conversions, bounds checks, constructors/defaults, overloaded calls, I/O, nonlocal exits, stored mutations, and abort possibilities. A recognized pure literal/arithmetic value can be warned about if the compiler proves its evaluation is defined and effect-free. An unknown function—even one with a pure-sounding name—is not a proof. Numeric operations that may trap in a debug profile are not removable merely because a release profile wraps.

**Acceptance:** positive no-op expressions; negative `print`, `abort`, throwing/trapping bounds or numeric paths, construction with effectful defaults, queue/poll operations, and unknown calls. No auto-fix.

### 6.3 Existing warning parity

Port existing redundant cast, redundant `&`, and avoidable copy warnings to rule IDs. Preserve the current warning fingerprint/dedup behavior through typecheck retries, clone checks, loops, overload resolution, and different specializations. A context-specific cast that changes width or rounding must never be labeled redundant just from its spelling.

**Acceptance:** old warning fixtures byte-for-byte unchanged under `goose --check` and `goose check`; `goose lint` produces a matching coded record for each warning with source origin and no duplicate.

### 6.4 `post_overflow_guard` (opt-in)

Recognize a concrete dataflow shape: a signed addition/subtraction of known width assigns a result; a subsequent conditional tries to identify overflow by comparing that result against a source operand, with an applicable nonnegative/monotonic contract. Show where arithmetic occurred and where the attempted guard occurs; require evidence that the guard is intended to detect that overflow. Never generalize this finding to unsigned modular algorithms or deliberate wraparound. Provide signed debug-before-guard and release-wrap explanation.

**Acceptance:** exact canonical positive and several negative patterns (pre-guard checks, unsigned wrap, arbitrary comparison, no declared numeric intent). Low-confidence cases emit only opt-in review hints with evidence; no suggested code rewrite applied.

### 6.5 `stale_slice_length` (opt-in)

Track retained slice creation, original array root, a provable same-root growth, and a later use whose intent/contract needs the new extent. Distinguish stale **length** from stale **element address**: Goose growth preserves appropriate references, while the slice's length is captured. Snapshot prefixes are legal. If growth alias identity is uncertain, no high-confidence finding.

**Acceptance:** stale length with dependent appended index, benign old-prefix snapshot, slice captured after growth, unrelated array growth, and unknown aliasing.

### 6.6 `specialization_fanout` (opt-in)

Reuse the compiler's checked `FnSpec` instances and root/type/function/destination contexts. Aggregate counts per source definition and selected entry set. Output exact counts and contributing contexts; identify profile/compilation root. This is a cost-analysis report, not a correctness error; avoid global defaults that cause false conclusions. It must not run the backend to guess runtime cost or normalize away root distinctions.

**Acceptance:** synthetic generics with predictable fanout, alternate entries, source clone dedup, stable report ordering, and unchanged program specialization counts.

### 6.7 `view_before_append_argument` and `foreign_container_index` (opt-in project contracts)

Specify a small `goose.lint-contracts.json` grammar with versioned, exact library identities and argument/result roles, e.g. `owner`, `view_of(owner)`, `append_to(owner)`, `index_of(owner)`, `consumes_index(owner)`. Implement only statically proven cases with accurate evaluation order, documented view-length and copy-subtree destination behavior. Unknown pointer/index provenance never proves a mismatch. A producer for document A passed to a consumer with document B is a finding only if producer/consumer owner identities are both known and unequal. Avoid assuming an integer's raw value or equal lengths imply owner compatibility.

**Acceptance:** two synthetic documents with equal-looking indices but distinct owners, a correct same-owner call, a destination document index from copy, view captured after append, view intentionally representing old prefix, and deliberately ambiguous aliases (abstain). Contract drift / missing APIs must fail configuration or appear explicitly incomplete, not silently skip.

---

## 7. Implementation milestones (do not reorder across dependencies)

Each milestone ends with source changes, targeted runnable tests, updated notes, and a working check. A coding agent must make local commits/checkpoints if its environment permits, but follow current repository instructions about pushes and upstream branch contamination. Keep unrelated formatter changes out.

### M0 — Reconnaissance, fixtures, and locked behavioral baseline

1. Read `AGENTS.md`, `README.md`, `docs/implementation.md` §§1–3, `docs/testing.md`, the latest issue #10, relevant compiler sources, `test/goose_in_goose/README.md`, and the current state of the checkout. Reconcile differences from audited SHA; record exact starting commit and toolchain versions.
2. Build the compiler with the documented CMake flow. Record compiler version, OS/architecture, native compiler/libc, flags, and suite/coverage limitations. Run representative `--check`, warning fixture, multi-test, and Goose-in-Goose tests before modifying code.
3. Inventory every current warning emitter, handling of queued warnings/cast verdicts, AST clone/source origin, parse location precision, import/package side effects, result-use shape, `qpoll`, and effect facts. Identify which rule facts need minimal new instrumentation.
4. Write failing characterization/expected-output fixtures for warning parity, fallible-result discard, unused pure expressions, source location spans, and clean JSONL, without reformatting existing `.goose` files.
5. Produce a short `docs/lint/DECISIONS.md` stating protocol boundaries, compatibility, no-network behavior, and why the Goose-in-Goose bootstrap parser is not reused.

**Gate M0:** Successful recorded baseline + first negative fixtures; no behavior change; clear compatibility decisions and traceable dependency map.

### M1 — Structured compiler diagnostics and source ranges

1. Introduce typed stable codes and an opt-in capture sink. Reclassify existing warning sites without changing the regular warning text or warning lifecycle.
2. Implement original-source spans/comments at the parser/lexer boundary, using a bounded side table and clone-origin mapping. Do not claim exact spans for original diagnostics where only a line is available.
3. Add deterministic encoding and duplicate handling. Verify cast warnings requiring all-specialization consensus and loop/overload retry behavior.
4. Add focused C++/compiler tests plus golden JSON records. Confirm existing `// warning:` fixture parity.

**Gate M1:** Same compiler warnings under all legacy commands; warnings acquire exact stable IDs and source-origin records; no parser acceptance changes.

### M2 — Semantic facts v1, bounded and verifiable

1. Add pre-optimizer fact extraction at the typecheck success boundary; never use optimized AST for source-lint proofs.
2. Export only necessary typed expression/call/result/effect/root/specialization/coverage data with deterministic IDs and valid source offsets. Separate fact truth from rule decision and unknown from false.
3. Define version, checksum/terminal marker, integrity and resource limits, missing-value semantics and error behavior; build malformed-stream tests.
4. Test clones and specialization-sensitive facts, imported modules, default arguments, multiple return values, checked/unchecked generic bodies, and legitimate legal references.
5. Ensure lint-mode package loading is offline by default; prove no target execution, generated-C compile or native sidecar execution. Report unsupported input honestly.

**Gate M2:** Two identical builds/runs of the same input produce byte-identical normalized facts; changing optimizer level does not alter pre-optimizer correctness facts (apart from declared profile metadata); corrupt facts fail.

### M3 — Goose-native engine, build, and integrated CLI

1. Implement Goose decoders/validators, fact graph model, rule registry, deterministic sorting, text/JSONL writers, summary/coverage, and exit-code classification.
2. Add `goose lint` verb, secure temporary transport, child invocation and cleanup; ensure JSONL cleanliness despite `RunProcess`'s combined output.
3. Add CMake `goose-lint` target with one-way dependency on the canonical compiler; build a relocatable standalone companion and package it with regular installations.
4. Implement the baseline `--help`, input errors, unsupported protocol failures, missing-companion failure, no-network default, CLI option parsing and text/JSONL smoke tests.
5. Dogfood a trivial rule on linter-owned `.goose` modules as early as possible; do not defer all self-lint until finalization.

**Gate M3:** `goose lint` runs from a relocated installed build, emits deterministic diagnostics and coverage, and fails nonzero on missing/corrupt companion or facts. Goose rules—not C++ source regexes—decide findings.

### M4 — Exact core results and existing warnings

1. Implement `discarded_failure` and `unchecked_poll_result` using exact API contracts, def/use, scalar/tuple result forms and unknown aliases.
2. Implement `unused_pure_value` with a conservative transitive effect lattice and debug/release observable behavior safeguards.
3. Surface existing `redundant_cast`, `redundant_reference_marker`, and `avoidable_reference_copy` warnings through their stable IDs.
4. Add per-rule positive/negative fixtures, imported API test, overload/specialization cases, parity against legacy `--check`, and evidence snapshots.

**Gate M4:** Six functional findings categories pass the proof matrix; no generic bool-based fallible warnings; no dropped effectful call; identical legacy compiler semantics.

### M5 — Policy, suppressions, baselines, coverage

1. Implement config selection/merging, group/severity changes, exact contracts, malformed config errors, and strict JSON schema.
2. Implement local comment suppressions with explicit reason, narrow statement binding, unused/unknown diagnostics; ensure comments in raw strings never count.
3. Implement baseline fingerprints, atomic explicit write, stale/duplicate detection, and drift tests; do not auto-mutate during lint.
4. Implement specialization/source coverage, unknown-site counters, `--require-complete`, and machine-readable error status.
5. Test CLI precedence and all five exit codes, including invalid source, missing imports, corrupt facts, stale suppression and denied finding.

**Gate M5:** A project can adopt lint without hiding new findings; CI can distinguish a clean run from a failed analyzer; policy behavior is deterministic.

### M6 — Bounded opt-in Goose-specific review and contracts

1. Implement `post_overflow_guard`, `stale_slice_length`, and `specialization_fanout` as restricted opt-in analyses with evidence and negative examples. Add report-level facts only for requested performance rules.
2. Implement exact-identity contract model and narrowly proven `view_before_append_argument` and `foreign_container_index` cases using synthetic standalone fixture APIs.
3. Add cost/complexity limits and explicit inconclusive outcomes; ensure no application source or private Aincrad3 dependency is needed.
4. Populate the full 65-entry RFC disposition inventory. Keep deferred rules absent from runnable registry or explicitly unavailable, never silent empty implementations.

**Gate M6:** All twelve v1 rule IDs are truly implemented with documented supported shapes and proper defaults; every remaining RFC candidate has a reasoned deferred disposition.

### M7 — Full-suite integration and performance qualification

1. Integrate `test/lint/` into the existing Python test runner or add a clearly invoked, documented dedicated runner; use the repository's real `// warning:` and positive/negative fixture conventions without changing their meaning.
2. Run supported platform CI: Linux, macOS, Windows, release/debug, `-O0`/`-O2` representative cases, JSON fixtures, and resource/path relocation; sanitizer/fuzz tests where suitable.
3. Compare before/after base-revision frontend wall time and peak memory on small programs, stdlib/sample imports, a moderate multi-module program, and a high-specialization workload. Warm up, alternate runs, record sample counts/variability, compiler/native toolchain and exact options. Distinguish parser/typecheck, fact extraction, Goose analysis, and total latency.
4. Measure lint-only overhead as well as normal `goose check` regression. Set practical budgets; a proposed release gate is **no statistically persuasive regression over ~5% in ordinary non-lint `goose check`**, and investigate **>20% total lint overhead** or **>1.5× peak memory** on representative medium projects. These are review thresholds, not claims about current performance. If better evidence suggests changes, document the measured tradeoff.
5. Verify no build-cycle or packaging regressions. Verify running from unrelated cwd with spaces/unicode in paths and concurrent invocations.

**Gate M7:** No accepted semantic regression, cross-platform delivery works, and performance tradeoffs are measured and documented rather than asserted.

### M8 — Dogfooding, release documentation, and final verification

1. Lint `tools/lint/main.goose` (with imports) under correctness/defaults, and lint selected `stdlib`/`samples` and `test/goose_in_goose/main.goose` for which entry semantics apply. Fix valid findings; use **narrow reasoned suppressions** for demonstrably intentional constructs.
2. Add ordinary CI self-lint gating with `--deny` for validated high-confidence rules; no blanket self-exemptions. Validate the compiler can rebuild the lint executable from clean artifacts.
3. Update `README.md`, CLI help, `docs/testing.md`, `docs/implementation.md`, and `docs/lint/*` for syntax, schema, limitations, profiles, cargo/CI-equivalent command examples, installation, and rules.
4. Run final full regression, new fixture suite, platform smoke matrix, offline/no-side-effects checks, JSON schema validator, and repeatability test. Inspect diff for accidental formatting or unrelated changes.
5. Produce a concise implementation report: commits/diff summary, exact tests run/results, measured performance, known limitations, each v1 rule's status, full 65-item disposition, and no unverified success claims.

**Gate M8 = campaign complete:** All global definition-of-done criteria below satisfied. No requirement to open a PR or push where repository instructions forbid it.

---

## 8. Verification matrix (mandatory)

| ID | Test | Expected behavior |
|---|---|---|
| A01 | Existing warning fixture before/after | Legacy `--check` messages/multiplicity identical; lint records stable coded warnings. |
| A02 | Warn in repeated check/loop and multiple clones | One source/evidence warning; specialization disagreement preserved where meaningful. |
| A03 | Simple `parse_int` success discarded | `discarded_failure`, precise status result evidence. |
| A04 | `parse_int` status tested, propagated, or contractually explained | No failure-discard finding. |
| A05 | Unrelated boolean ignored | No `discarded_failure`. |
| A06 | `qpoll<T>()` consumed as scalar | `unchecked_poll_result`. |
| A07 | `qpoll<T>()` status checked | No unchecked-poll finding. |
| A08 | Pure discarded value vs effectful/possibly trapping expression | Only the proven no-effect case warned. |
| A09 | Call default argument with effects | No incorrect pure-expression finding. |
| A10 | Signed post-overflow guard vs unsigned modular operation | Opt-in review distinguishes them. |
| A11 | Slice captured before push, then newly added element expected | Supported stale-view finding with correct owner. |
| A12 | Deliberate old-prefix snapshot | No correctness warning; review hint only if explicitly requested and meaningful. |
| A13 | Distinct document owners with equal integer indexes | Contract-aware foreign-owner finding. |
| A14 | Same owner / subtree index owned by destination | No false owner mismatch. |
| A15 | View capture after append | No old-length finding. |
| A16 | Same source with two generic specializations | Honest coverage, original-node mapping, stable distinct contextual evidence. |
| A17 | Unused generic function | Report unchecked semantic coverage, do not assume it was validated. |
| A18 | Malformed Goose source | Source diagnostic/exit 2; no clean lint result. |
| A19 | Missing offline import | Explicit failed input/coverage; no network or silent subset analysis. |
| A20 | Corrupt/truncated/incompatible facts | Exit 4, machine-readable failure, no findings falsely claimed complete. |
| A21 | Suppression on code, preceding comment, string literal, stale directive | Only valid narrow directives apply; stale/invalid handling. |
| A22 | Baseline match, stale entry, new finding, collision | Existing instances identified, new instances visible, stale reported. |
| A23 | `--deny`, `--allow`, group, CLI vs config | Documented precedence and exit 0/1/3. |
| A24 | JSONL with invalid program/companion failure | Valid JSONL records only, correct nonzero status. |
| A25 | Different cwd, CRLF, UTF-8, tabs, raw multiline, Windows paths | Stable normalized paths, correct byte spans or honest line precision. |
| A26 | Two byte-identical runs | Identical normalized facts/output; no pointer/temp-path instability. |
| A27 | High specialization and many imported files | Bounded memory/latency, deterministic output, no truncation masked as success. |
| A28 | Relocate packaged `goose` + `goose-lint` | `goose lint` works without source checkout/Python/toolchain rebuild. |
| A29 | Lint engine's own Goose source | Build and self-lint cleanly under selected policy. |
| A30 | Goose-in-Goose bootstrap and normal full suite | Unchanged bootstrap fixed point and existing compiler behavior. |

Every shipped rule must also have a **rule contract fixture** recording: `code`, group, severity, confidence, triggering proof, non-triggering patterns, example text/JSON, context and cost. Use regression test names that identify the behavior, not arbitrary issue numbers.

### Invariant/property tests worth adding

- Adding whitespace or CRLF should not change finding codes/evidence; source byte ranges legitimately change.
- Changing specialization traversal order must not change normalized diagnostics.
- Removing a documented fallible contract removes the finding, never turns unknown bool into assumed failure.
- A subexpression changing from proven pure to unknown/effectful cannot increase the certainty of `unused_pure_value`.
- An alias fact weakening from distinct to unknown cannot create a high-confidence `foreign_container_index` mismatch.
- Adding an uninstantiated generic cannot silently increase semantic coverage.
- A corrupted or truncated fact stream cannot be accepted as zero findings.
- A suppression or baseline cannot hide a new distinct finding in the same file.
- `goose lint` cannot run target `main` or invoke target-defined native build commands.

---

## 9. Safety, compatibility, and performance decisions

### A. Soundness language

A lint is not a compiler theorem unless its evidence really supports that claim. Represent at least `proven`, `review`, and `inconclusive/skipped`. Confidence and severity are separate. Unknown aliases, uncalled generic bodies, unknown effects, and undeclared application contracts cannot be replaced with default assumptions.

### B. Debug/release semantics

Preserve Goose-specific behavior: signed overflow/conversions can differ between checked/debug and release configurations; unsigned wrapping is defined; Euclidean integer remainder differs from C expectations; references and slices have Goose-specific lifetime/growth rules; shallow `const` is legal. No imported Rust/C assumptions.

### C. Frontend evolution

The private fact schema can evolve through matched compiler/companion revisions; the public diagnostic schema and stable rule IDs require compatibility reviews. Add versioned fixtures for each field. When a future compiler pass changes its internal AST, the encoder—not user Goose code—must preserve the fact contract or explicitly bump the version.

### D. Fail closed, but report honestly

Cannot load program/imports: unsuccessful source/input analysis. Cannot decode facts/companion: tool error. Unsupported individual proof: no claim and an explicit skipped counter. An unused/uninstantiated generic: known coverage limitation. These are four different states; do not flatten them to "lint passed".

### E. Resource usage

Never serialize source contents by default; provide source hashes/offsets instead. Bound input JSONL record sizes and overall fact count, cap diagnostic volume with an explicit truncation/error status, and avoid loading C++ AST-derived facts twice when unnecessary. Goose stdlib's current file-reading interfaces may lead to whole-file reads: benchmark them and, if necessary, add a modest streaming reader/decoder rather than deploying a tool that OOMs on a realistic project. Never truncate output with success status.

### F. Security/privacy

The linter is a local developer tool. Do not upload source/facts, fetch packages silently, execute target programs, use shell interpolation, expose secrets in generated diagnostics, or leave facts streams world-readable after failure. Malicious filenames/config JSON must not cause command injection or overwrite arbitrary files. Baseline writes must be explicit and atomic.

---

## 10. Autonomous agent operating protocol

**At start:** Inspect the actual checkout and record its HEAD, working-tree status, current `AGENTS.md`, host toolchain, and relevant docs. If the inspected SHA differs from this campaign's source baseline, adapt to the current implementation and record what changed. Do not reset or overwrite unrelated user changes. Work in a local feature branch or carefully isolated commit sequence according to repository policy.

**Execution:** Complete milestones sequentially. For every new rule, first add minimal positive and counterexample fixtures, then implement the facts/rule, then test the end-to-end CLI record. Re-run the narrow suite at each checkpoint and the full suite at M7/M8. Keep C++ changes narrowly semantic and Goose code responsible for policy. Update schemas/docs with the same commit as behavior changes. Keep every change focused enough to revert independently.

**Autonomous decisions:** When a rule is under-specified, favor a smaller sound shape over guessing a broad intent. Record the adopted subset and add counterexamples. Do not widen a default rule's evidence requirements to make the fixture pass. If an intended opt-in rule needs substantial new solver infrastructure, implement the precise subset described here and record its analysis coverage; if even that cannot be truthful, mark the milestone blocked in the final report rather than shipping a placebo. The 65-rule inventory preserves future scope.

**Failure response:** Fix regressions, do not disable tests, suppress compiler errors, or loosen invariant gates. If a host lacks a required optional platform/toolchain, run the feasible checks and report the exact missing verification. Never state a test passed unless it was run. Do not skip final docs and packaging because a few rule tests passed.

**Repository hygiene:** Read and obey `AGENTS.md`; notably do not reformat existing Goose fixtures, do not mix upstream fix work with fork tooling, and do not `git push` in violation of current repository conventions. A local diff/commit plus report is a valid delivery; publishing requires separate authorization/workflow.

**Final agent report format:**

1. Starting and ending revisions; changed files and architecture decisions.
2. Implemented rules (12 IDs) with proof scope, default state, and tests.
3. Deferred RFC rule ledger (53 IDs), with promotion requirements.
4. Exact commands and results for the full suite, lint suite, bootstrap, CI/platform checks, security/offline checks and installed-package smoke tests.
5. Before/after build/check/lint timing and peak memory with hardware/compiler/native toolchain and sample counts.
6. Any unverified gates, remaining limitations, compatibility notes, or blockers; no invented passing claims.

---

## 11. Definition of done (hard release checklist)

- [ ] `goose lint app.goose` works after a clean supported build and from a relocated installation, with the Goose-native companion included.
- [ ] The canonical C++ parser/typechecker is reused; no second grammar or semantic checker was introduced.
- [ ] Meaningful rule logic is implemented in Goose, compiles normally, and lints its own source.
- [ ] Structured warning/diagnostic bridge preserves existing human warning behavior and deduplication under legacy commands.
- [ ] Public diagnostics and private facts each have versioned schemas, integrity checks, stable record ordering, documented coverage and valid error envelopes.
- [ ] New rule spans are exact where supported; legacy line-only fallbacks are honest; imports/clones are correctly mapped.
- [ ] All 12 listed v1 rule IDs have working analysis, evidence, fixture matrix and legitimate counterexamples; default/opt-in separation is enforced.
- [ ] Full 65-ID issue catalog is classified (12 implemented, 53 deferred), with no empty rule stubs misrepresented as implemented.
- [ ] Suppressions and baselines cannot silently hide new unrelated findings; stale/unknown cases are diagnosed.
- [ ] All exit statuses and JSONL validity are tested under success, denied, invalid source, invalid config and tool failure.
- [ ] Linting performs no target execution or hidden network/native build; missing imports and unsupported inputs fail explicitly.
- [ ] Existing tests, including `goose_in_goose` bootstrap, preserve their behavior; focused and cross-platform checks pass or are explicitly documented as not run.
- [ ] Performance is measured against the exact starting revision, for non-lint checks and lint workloads, without hand-waving.
- [ ] README, implementation/testing documentation, CLI help, schemas, rule reference, limitations and release packaging are updated.
- [ ] Final report contains reproducible commands, actual results, measured tradeoffs, and any remaining caveats.

**Completion does not mean implementing every rule candidate in issue #10.** It means the full platform, precisely scoped shipped rules, adoption workflow, and dogfooding are complete, while future research candidates are explicitly accounted for. A false-positive-prone linter with 65 nominal rules is worse than a trustworthy tool with 12.

---

## 12. Source map and grounding

Source inspection for this campaign used the connected GitHub repository at `a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d`, corresponding to the issue's stated baseline. Relevant evidence:

- [Issue #10](https://github.com/joshuarli/goose/issues/10) — 65 candidate rule catalog, semantic layering, diagnostic contract, coverage, explicit warning against enabling all rules by default.
- [Production pipeline: `docs/implementation.md`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/docs/implementation.md) — parse, resolve, typecheck, optimize, bounds-check-elimination, code generation; origin and specialization semantics.
- [`src/main.cpp`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/src/main.cpp) — verbs, option parsing, typecheck/optimizer boundary, toolchain/frontend mode.
- [`src/typecheck.h`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/src/typecheck.h) — warning deferral/dedup, source origin, instantiation chains.
- [`src/ast.h`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/src/ast.h) — `Line`, `Node::Origin`, owned typed AST and specialization records.
- [`src/lexer.h`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/src/lexer.h) and [`src/parser.h`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/src/parser.h) — canonical scanner and recursive-descent parser.
- [`test/goose_in_goose/README.md`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/test/goose_in_goose/README.md) — Goose-written compiler is only a subset bootstrap fixture; not language reference.
- [`docs/testing.md`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/docs/testing.md) and [`test/run_tests.py`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/test/run_tests.py) — existing warning markers and full regression profiles.
- [`stdlib/std.goose`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/stdlib/std.goose) — actual `parse_int` trailing boolean.
- [`stdlib/os.goose`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/stdlib/os.goose) and [`stdlib/json.goose`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/stdlib/json.goose) — Goose-native tooling primitives.
- [`src/process.h`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/src/process.h) and [`CMakeLists.txt`](https://github.com/joshuarli/goose/blob/a03a2ca6fefd8cb2406239cf1edde3bb256ebe7d/CMakeLists.txt) — portable child-process capabilities and companion build integration.

**Important scope note:** This is a source-informed implementation campaign, **not** a claim that the proposed CLI/rules already exist or that tests were executed as part of writing it. Every implementation and performance assertion above is an acceptance target to verify in the agent's actual checkout.
