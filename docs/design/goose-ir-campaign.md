# Campaign: Lean-backed Goose semantics, Goose IR, and build scalability

**Status:** winding down. Performance qualification and the three universal proof obligations remain open. Pushes remain unauthorized.
**Branch:** `goose-ir`. The branch was rebased onto local `master` at `b7885160`.
**Contracts:** [specification](goose-ir-spec.md), [validation plan](goose-ir-validation.md).

## Current proof work

The demand-prefix proofs cover supported scalar and short-circuit expressions, local or global clears, and assignments to local or global places, their fields, indexed elements and indexed array fields. Mixed blocks carry accepted frames through scope entry and exit. They cover successful prefixes and non-timeout stops, with no loop context in the block stop proofs. Assignment values include literals, arithmetic, comparisons, short-circuit expressions, and direct reads. Direct reads require the value type to be a valid reference target.

Construction proofs preserve accepted worlds and frames across every outcome of byte-owner value evaluation, byte-owner global initialization and checked sequences of unnamed byte-owner declarations. A byte-only module with no entry tail retains an accepted world and satisfies the destination-trace protocol at its actual result for every fuel; the world result also covers arbitrary interleavings of byte declarations and recursive scalar expression statements with byte-owner globals and no tail. Exit proofs connect a nested byte return through an intervening activation to its matching outer handler, under the recorded receiver, setup and successful-build assumptions. Output and outside-scope entries are preserved relative to the post-build state. General construction preservation, other exits, loops, calls, returns, and whole-function cursor reconstruction remain open. These results do not close `TH-CON-01`, `TH-EXIT-01`, `TH-LOWER-03`, or their gates. The current assumptions and limits are recorded in `semantics/coverage.json`.

Scoped proof closures use pinned Lean 4.35.0 and the allowed axioms. The adjacent `lean4` checkout is at `origin/master` revision `f4856ef9`, with stage1 built separately. Comprehensive corpora, full Lean and native qualification, five-kernel replay, and final performance qualification remain manual-only named workloads under the owner's existing instruction. No performance budget or release gate is waived.

## Historical resume handoff (2026-10-26)

**Resume:** “Resume the paused Goose IR campaign from this handoff; reread current instructions and finish the remaining accepted-execution proofs.” First run `git status --short --branch`. On an authorized resume, cancel campaign closeout if still active, reread the applicable skills, and perform the parent steering checkpoint before selecting work. Recreate selected worktrees under `.work/wt/` from their preserved branches. Do not automatically replay historical lane commits or repeat unchanged qualification.

**State:** the last accepted source revision is `0df2c602`. Later commits record cleanup and this handoff. No integrated code is awaiting a known failing check. There are no in-flight lanes. Local commits remain authorized by the requested workflow; pushes remain unauthorized. Other owner workflows may update remote refs independently.

Winddown integrated all ready coherent lane changes: canonical checker cursors and successors, literal/Boolean and negation prefix decomposition, shared unit/value block assembly, discarded-expression prefix transfer, actual reservation ticket append, initializer witness alignment, and the canonical callee source-frame factory. The proof APIs retain actual child metadata and initializer callee tables. These changes do not alter compiler or evaluator behavior. The earlier limited-array capture fixes and raw-module validation repair remain integrated.

**Direction:** whole-block prefix composition now consumes actual child prefixes and retains the real execution remainder. It covers clear-only bodies with literal/Boolean values, plus abstract expression-family composition for negation and discarded expressions. The retained-index initializer pilot preserves its nonempty run map through every prefix, conditional on source validation. Its validation is confirmed at runtime; no closed kernel validation proof is claimed.

The limiting work is the accepted mutual induction. Construction receipts must link actual current objects, allocation rows, receiving ancestry and lifetime before they can support separation. The qualified conditional family draft is not a sufficient accepted-world invariant. Callee source frames are canonical, but actual argument execution, final-heap content provenance, parameter binding and the runtime world/frame still need one assembled proof. General expression/statement recursion, abnormal block exits, loops, calls, returns and all-runtime demand-root assembly remain unfinished. `TH-CON-01`, `TH-EXIT-01`, `TH-LOWER-03` and their campaign gates remain open.

The next substantive delivery is a source-derived construction invariant with one complete accepted evaluator case, then preservation through the remaining native families. Strengthen or replace the parked receipts before extending their family. On the lowering side, extend the existing prefix engine rather than adding a second one or assuming successful whole-source evaluation. Reassess after a real accepted case or a demonstrated contradiction. Comprehensive corpora, full Lean/native qualification, five-kernel replay and final performance qualification remain manual-only named workloads under the owner's existing instruction; scoped checks do not select them. No performance budget or release gate was waived.

**Parked proof designs:**

| Branch | Checkpoint | Finding and retry condition |
| --- | --- | --- |
| `campaign/afk-family` | `81ffccd6` | Qualified conditional Native23 family declaration and Boolean case. Current-row, storage and lifetime links in its receipt prerequisite are underconstrained. Repair those links and derive initial/preserved validity before claiming accepted execution. |
| `campaign/afk-construction` | `881f7635` | Draft owning receipts. Its useful source-position prerequisite `71003ffb` is integrated as `1c163465`; the receipts are deliberately excluded. |
| `campaign/afk-construction-receipts-draft` | `21a33526` | Obsolete earlier family snapshot, preserved for design comparison only. |

Accepted work from `campaign/afk-demand`, `campaign/afk-short-circuit`, `campaign/afk-construct-roots`, `campaign/afk-exit`, and `campaign/afk-allocation` is integrated. Their checkouts were retired. Other retained unmerged refs are frozen historical or owner-managed snapshots, listed in [the cleanup record](goose-ir-winddown-cleanup.md#retained-unmerged-refs); branch history alone does not identify missing patches. No historical source is implicitly selected for resumption.

**Cleanup:** 23 completed campaign checkouts were removed with Git, preserving every branch. `.work/` shrank from 80.6 GB to 11.6 GB. About 9.2 GB is compressed evidence: qualified exports, native artifacts, logs, repro inputs and performance results under `.work/archive/`. Each new archive passed integrity and tar-list checks before the originals were removed. Current scratch uses about 401 MB. The cleanup record names the archives and four small unregistered source snapshots retained pending ownership/source review. Durable campaign state is committed; archived scratch is optional evidence rather than the only copy of any campaign source.

**Retained registered worktrees:** all four are clean and allowed by the closeout guard. The Aincrad trees belong to separate owner work; none is an active IR proof lane.

| Path under `.work/wt/` | Branch or HEAD | Current consumer |
| --- | --- | --- |
| `accelerate-perf-baseline` | `campaign/accelerate-perf-baseline`, `24ba0840` | Frozen compiler baseline for deferred performance comparison. |
| `aincrad3-goose-storage-whole-region` | `fix/linux-whole-region-advice`, `b7b9e0e3` | Owner-managed Aincrad storage experiment. |
| `aincrad3-goose-whole-region-master` | `fix/linux-whole-region-master`, `ed85e2e5` | Owner-managed Aincrad upstream comparison. |
| `goose-master-2ad09c99` | detached `2ad09c99` | Immutable Aincrad upstream baseline, relocated with owner approval. |

The other approved external relocation was followed by concurrent owner cleanup: the runtime edits are preserved at `85fd984f` on `fix/linux-current-whole-region-advice-20261023`, and its checkout is retired. No registered external worktree remains.

**Verified:** the final lowering group passes 201 modules and the final construction/callee/reservation group passes 245 modules under pinned Lean 4.35.0. The earlier 346-module source-position/negation group also passed; the changed construction dependencies were rechecked in the final group. Seven final selected axiom checks use only `propext`, `Classical.choice` and `Quot.sound`. `git diff --check` passes. No formatter, new corpus run, native semantic rebuild, independent-kernel replay or performance measurement was run for winddown. The known full-proof and performance gaps remain unmet.

Reboot checks cover clean registered worktrees, preserved branch refs, ignored disk-backed `.work/`, no campaign worker/build process, and the configured trusted Stop command. The API cannot invoke interactive `/hooks`; its configuration and actual closeout command were checked directly. The campaign goal is paused. The current user has no crontab; system-wide schedules were not audited.

Rehearse inspection from the repository root without starting work:

```sh
env -i HOME="$HOME" PATH="$PATH" sh -c '
git status --short --branch
git log -1 --oneline 0df2c602
git show campaign/afk-family:semantics/Goose/Proofs/ConstructionAcceptedExecutionFamily.lean >/dev/null
git show campaign/afk-construction:semantics/Goose/Proofs/ConstructionAcceptedOwningOrigins.lean >/dev/null
git show campaign/afk-construction-receipts-draft:semantics/Goose/Proofs/ConstructionAcceptedExecutionFamily.lean >/dev/null
git worktree list --porcelain
test -f docs/design/goose-ir-winddown-cleanup.md
test -x /home/josh/.local/lib/lean4/v4.35.0/bin/lean
'
```

## Unattended completion (2026-10-25)

The owner requested continued execution until campaign completion and invoked AFK.
Local checkpoint `1197e996` contains limited-array capture support and its focused C++ and runtime checks.
Its 310-module Lean closure now passes under pinned 4.35.0 after detecting an earlier 4.34.1 PATH mismatch.
All current lanes use the pinned 4.35.0 explicitly.

Isolated lanes own source-demand correspondence (`campaign/afk-demand`),
construction backing and ownership (`campaign/afk-construction`), exit storage observations (`campaign/afk-exit`), and accepted runtime root correspondence (`campaign/afk-construct-roots`).
The expression lane, `campaign/afk-short-circuit`, owns compositional expression-prefix traversal.
The construction evaluator family has one implementation owner on `campaign/afk-family`; the construction lane supplies its source-position and physical-owner prerequisites.
Their worktrees live under `.work/wt/`.
The integrator owns verification and profile completeness.
The next proof milestone is an accepted-execution invariant, not another endpoint-only wrapper.
The current runtime protocol theorem preserves protocol metadata but does not establish object backing or byte separation.
Construction and exit proofs must derive those properties from accepted reachable execution.

The semantic runner now checks high GIR validation, execution, re-encoding and Core agreement for pilot and shrink as well as construction.
Three hostile GIR-oracle controls fail before the repair and pass afterward; 30 classified self-test cases remain correct.
Four selected pilot and shrink sources agree through the expanded runner, with the rebindable-reference control still unsupported.
The closure helper now rejects a mismatched Lean release before compiling any module; its 14 tests pass.

Integrated proof components preserve successful packed scans and fixed-value reads across protected byte prefixes.
Accepted validation supplies the required struct field bounds.
Construction references now have explicit source-root interpretations, checked argument/result substitution, and local binding preservation.
These components pass focused 4.35.0 closures but do not close the universal construction, exit or demand invariants.

The source root checker now owns `RootAlias`, `RootSetsOverlap` and `AliasClosure`.
Accepted module validation supplies the alias closure and actual checked body environments;
the former provisional proof vocabulary has been removed.
Expanded equality proofs retain the checker's context-before-initializer order and errors.
Reference-slice content correspondence distinguishes the holder's root from its pointee's roots.
Grounded direct and forwarded calls validate and print `7`; self-content substitutions fail their actual call checks.
Scope-entry transport still requires freshness and visible-local premises that the accepted execution induction must derive.

Integrated construction components derive backing after accepted arbitrary byte-owner initialization,
packed-count completion, fresh allocation, and complete repeat-element fill loops.
Exit components derive payload relocation, completed landing, rooted read preservation and live anchor traversal
under explicit receiving geometry and parent-readiness premises.
The joint typed source-action induction must establish those premises for reachable execution.
Exact retained operand rows now reject missing rows, wrong SSA identities and removed resizable backing;
canonical instruction ownership and full source-demand coverage remain open.

The shared construction source frame now carries exact typing and root-checker cursors.
Its root facts are indexed by the actual escaping and callee-name tables.
Its accepted entry factory derives the actual implementation, checker witnesses, fresh activation and alias completeness;
it does not assert storage backing for an arbitrary input state.
The owned world now includes ghost root types and nominal layout conformance.
Its initial factory requires successful validation and derives conformance for every declared global.
Actual fresh owner binding preserves the world without receiving or pending frames;
binding a stored value to the next global advances the initialized prefix.
Fresh destination allocation derives byte-cut protection and excludes its new row from existing named values.
The live-carrier singleton theorem derives native landing success, backing, receiving readiness,
and outside-root observations from exact row permissions and receiving geometry.
Sequential carrier exclusions and those permissions still need the joint execution induction.
Successful native fixed decoding, stored-element decoding, path reads and location reads preserve result typing and backing.
These success theorems do not establish path validity or fault freedom.
Generic demand factories derive instruction lookup from real builder extension and emission equations.
One accepted limited-array initializer has static source ownership at every runtime point;
address, snapshot, load and checked-index components now derive dynamic transfer from actual runtime steps.
Short-circuit controls retain a live sample through an actual limited-owner clear from length one to zero for AND and OR.
Independent review found no scoped proof defect and prompted that stronger control.
Full source-action coverage, body/loop continuations and call/return assembly remain open.

Accepted initialization controls prevent two overstrong assumptions:
an unused reference to a later global can be created before that global exists,
and a static slice parameter can read synthetic roots beyond the module's declared-global table.
Typing limits, actual read-effect availability and synthetic-root identity remain separate.

The latest integrated construction check passes 231 selected modules under pinned Lean 4.35.0,
covering physical-key registration, entry freshness, successful-read typing, fixed encoding widths and element-write geometry.
A complementary 220-module check passes allocation-world preservation with the same strengthened registration contract.
The fixed element-builder case consumes those encoding and write proofs; its 222 dependency sources match the qualified lane check exactly.
The combined source-factory, block, slice and length-query check passes 203 modules on the integrated tree.
A concrete clear-and-literal block starts at an actual reachable GIR initializer point and preserves its sampled run at every runtime prefix of its five-instruction span, including independently chosen instruction fuel.
Its only input premise is acceptance of the source module; runtime validation confirms that fixture, while no closed kernel proof of its validation equality is claimed.
All retained axiom checks use only `propext`, `Classical.choice` and `Quot.sound`.
These scoped checks do not qualify the whole project or close the three universal obligations.
Stable-key C++ unit tests pass after sharing the visitation helper.

Review identified a missing link between the construction frame and the world's backed roots.
The central invariant will cover every present physical object in ordinary states, with explicit receiving-phase exceptions tied to actual surrender, retirement and cleanup evidence.
An extension must preserve the existing encoded prefix; exclusive replacement instead excludes receiver access until repair.
The ordinary and receiving worlds share structural facts, while retaining distinct global-backing requirements.
The joint evaluator family and its preservation proof remain unfinished.
Action-local checker replay now preserves metadata and the exact source cursors while clearing accumulated effects.
The accepted invocation proof still needs to extract and use those local effects: accumulated reads contain history, while subtracting deduplicated sets loses repeated reads.
Unused references to future globals remain allowed; no blanket pointee-liveness or path-totality assumption is justified.

The shared world, source-owner factories and their selected consumers pass a coherent 441-module Lean 4.35.0 check.
A complementary 248-module check covers conditional content-root correspondence, parameter values, successful reference reads and accepted world consumers.
Actual parameter binding now derives content correspondence from the final caller heap and checked argument roots.
Unused reference parameters need no content row; actual reads and stores still require their native checker evidence.
Fresh call roots are older than the callee activation, without an assumed disjointness between parameter aliases.

Full demand closure needs one prefix-decomposition family joining actual context/global ownership, generated occurrences and required rows with source frames and locally extended maps.
Completed source simulations do not cover arbitrary prefixes of diverging loops.
Statement sequencing must pass the residual prefix after a completed child; call entry must use the actual callee selection.
Canonical frame-only predicates remain internal projections, not substitutes for that joined witness.
The prefix family now fixes the actual source owner and preserves real consumed and residual instruction prefixes.
Statement sequencing passes only a completed normal child's residual prefix to the next statement.
Literal and boolean expressions derive source completion from one actual constant instruction; a zero-step prefix retains the exact entry frame and generated site.
Unit and value blocks share one body-prefix assembly and consume scope exit only after their actual body and value prefixes complete.
The retained-index clear-and-literal initializer now instantiates that whole-block assembly for arbitrary runtime prefixes.
Its source-validation equality remains an explicit premise, confirmed by runtime validation rather than a claimed closed kernel proof.
Independent source review found no defect in the leaf, clear-body and shared-leave composition.
The integrated expression-prefix and construction-content group passes 169 modules; the whole-block pilot and abort group passes 155 modules.
The seven selected integrated axiom checks use only the standard three allowed axioms.
Composite expressions, general statements, abnormal block exits, loops and calls remain open.

An isolated report experiment replaces per-node hash allocations in report walks with a pointer set.
Five interleaved samples per condition on Aincrad3 checking, using Clang Release with libtcc and native layers disabled,
give report-on CPU medians of 5.842 seconds before and 5.651 seconds after;
observed ranges are 5.822–5.973 and 5.611–5.795 seconds.
Report-off ranges overlap. Non-timing reports and generated C match exactly on the bounded controls.
The binary grows by 264 bytes, and peak process RSS remains below 1.73 GB.
Candidate report overhead is 12.7%, so the proposed 10% cap remains unmet.
This experiment does not replace production-configuration qualification.

Function-value key numbering now shares that pointer-set implementation with both report walks.
The same five-sample protocol compares the retained node-set compiler with this additional change:
report-on CPU medians are 5.834 and 5.655 seconds, with ranges 5.816–5.972 and 5.553–5.769 seconds.
Report-off ranges overlap, exact non-timing outputs agree, and the binary shrinks by 16 bytes.
Measured report overhead remains 11.5%, above the proposed cap.
A separate single-varying-dimension fast path was discarded: its report-on median rose by 0.3% within overlapping ranges.
A borrowed cached-variable-name trial was also discarded: its 0.8% median reduction was within the observed spread.

## Feature-completion priority (2026-10-25)

The owner redirected the campaign toward feature completeness using the test-pyramid philosophy.
The compiler now exports static limited-array capacity queries and immutable reference
captures in nested functions. Capacity queries evaluate their receiver exactly once,
including effects and aborts. Captures preserve reference identity and pointee mutability.
Nested functions can also mutate the contents and length of captured `let` limited arrays.
Whole-owner borrows use contents permission without making the original binding rebindable.
Rebindable reference slots remain explicitly unsupported.
Existing independent Core evaluation and exact runtime expectations are the feature oracles.

The integrated Debug compiler passes three selected Core/GIR cases for these features,
including receiver-abort ordering. The mutable-reference-slot control retains exactly
the `captured-reference` rejection. New fixture layout and whitespace checks pass.
The feature lanes also checked exact legacy output and existing capture controls.

The two limited-capture cases match exact legacy and native GIR output.
Core and GIR evaluation agree in both numeric profiles through the interpreted semantic commands.
The C++ GIR verifier suite covers explicit limited-owner borrows and rejects raw binding addresses and readonly borrows.
The rebindable-reference capture control retains its `captured-reference` rejection.
The limited-borrow guards and permission proofs pass their 310-module dependency closure under pinned Lean 4.35.0.
These checks do not qualify the whole project or its performance gates.

Combining the limited capture with an owned-array call exposed a construction-profile permission mismatch.
The compiler exported the supported program, but the Core construction checker rejected its mutable argument;
the construction GIR checker also inferred a readonly limited-owner address.
Both now use contents permission for limited owners, matching the existing grow-owner rule.
Direct reference and argument guards fail before the repair and pass afterward;
readonly limited references still reject mutable access and allow readonly access.
The new source regression passes fresh interpreted Core/GIR validation, execution, re-encoding and agreement,
plus native GIR O0/O2 output `2\n0\n1\n`; fresh Core debug execution matches too.
These checks reuse current Main runtime commands without its Audit import; no new native semantic executable or global qualification is claimed.

The typed-writer work also exposed a raw-module validation defect: a fill targeting an array of grow owners
passed validation but evaluated to nested fixed values that did not represent its declared type.
Fill now checks constructibility, as array literals already do.
Construction GIR inline literals require constructible types, and inline fills also reject nonfixed layouts that need receiving destinations.
The failing Core and GIR rejection guards now pass; ordinary fixed fills and valid receiving-based nested fills remain accepted.
The 39-module check includes the existing construction GIR and typing/runtime controls.
Compiler acceptance and evaluation code are unchanged.

[`accepted_callee_parameter_prologue`](../../semantics/Goose/Lower/DemandParameterPrologue.lean)
connects every parameter prefix to actual GIR execution, including the empty and complete prefixes.
It derives the prefix cursor and preserves realized suspended caller value and run maps.
The focused Lean check compiles the two new modules and reuses 117 unchanged qualified imports.
Boolean and readonly-reference call checks cover every prefix. The boolean check also
connects its partial prefix to the actual fuel-13 timeout.
Integration leaves these semantic sources and dependencies unchanged, so that evidence is reused.
The new component has not undergone the manual whole-project axiom and independent-kernel qualification.

Normal iteration runs the changed regression and relevant controls through exact native selectors.
A compiler change may rebuild the Debug `goose` target. A proof change checks its changed
modules against imports whose source and dependencies still match the qualified cache.
Reuse the existing native semantic tool when its interpreter and schema are unchanged.
The semantic runner rejects unknown `--case` names before execution.

Comprehensive baselines, whole corpora, exhaustive matrices, complete Lean/native qualification
and five-kernel replays are manual-only workloads. Run one only after an explicit request
for that named workload. Completing a focused change does not automatically select them.
Keep their existing requirements visible without treating a scoped pass as global acceptance.
Do not wait for or retry performance gates during feature implementation.
Deferred timing remains unmet and cannot qualify release or campaign closure.

## Production qualification update (2026-10-25)

Compiler backend sources through `02d57ad3` pass the full baseline, including
678 native programs, 798 JIT programs, bootstrap, rejection tests and samples.
Both GIR source checks pass. The GIR units corpus passes 264 supported programs
with zero failures. Its 597 skips comprise 545 explicit unsupported programs,
49 native-layer programs, one parse-only fixture, one extern-function fixture,
and one captured-reference fixture.

The same compiler passes Aincrad3 E00–E03 structural reuse checks.
E01 performs no native compilation and skips linking. E02 changes only the locations
unit. E03 changes only one code unit. Each edit reuses the other 458 objects.
Edited rows verify reuse against recompilation. Their durations are not timing evidence.

The later report-only fix `3469527e` separates `native_build` from frontend phases
and charges unit emission to `write_output`, rather than report collection.
The new regression fails before the fix and passes with both Debug and Release compilers.
It checks native timing contains the actual compiler and link intervals and stays outside
`frontend_phases`. Existing units-builder contract probes and seven Python checks also pass.
No code-generation or language behavior changes in this fix. The Release size remains 10,415,648 bytes.

Logical checkpoint `cff3a6b6` passes all 2,656 Goose and Main source modules.
Its fresh native and interpreted audits match byte-for-byte on 217 unique claims,
using only `Classical.choice`, `Quot.sound` and `propext`.
All five independent kernels accept fresh exports of the 217 claims and `Main.main`.
Their union of 44,732 logical dependencies is covered by 45,251 exported constants.
The largest checker uses 4,443,254,784 bytes RSS. The coverage reader uses 6,498,000,896 bytes.
Both stay below the 8 GiB budget. This qualification excludes native code generation,
external implementations and module initialization code.

The full conformance run at `0639f2d4` records 105 pilot agreements, two explicit
unsupported features, three construction agreements and all nine native construction
trace fixtures across both numeric profiles and O0/O2.
The model definitions are unchanged at `cff3a6b6`. Its native audit and one pilot,
one construction and one trace fixture pass after the new proof-module imports.
Bounded generated-C checks at seed 20261025 complete 12 cases in each of six lanes
with the full Goose/C optimization matrix and ASan/UBSan.
All 72 legacy cases pass. Five lanes give 60 Core and GIR agreements.
The 12 aggregate cases report explicit unsupported elementwise arithmetic in Core and GIR.

Alias validation now rejects shrinking through retained interior references or slices,
checks mapped callee effects, and admits alias-free grow clears.
Initialized holders stay protected until scope exit, including after their last use.
Bindings still being initialized do not protect their future roots.
Independent review reproduced the initializer over-rejection and verified its correction.

The checked proof components now include short-circuit transfer, indexed operand replay,
exact fill-source byte frames, rooted owner backing and accepted parameter-prefix cursors.
The proof API names are now `DemandInstructionStep` and `DemandPrefix`, replacing
`DemandLinearStep` and `DemandLinearPrefix`. The source tree uses the new names throughout.
The claim ledger records their assumptions and limits. A checked input countermodel shows
why logical type and shape alone cannot supply storage backing.
Two other countermodels reject endpoint-only prefix lifting and exact Core/GIR timeout-state matching.
They do not refute the requested lifetime theorem.

The remaining proof work is substantive:

- `TH-LOWER-03` still needs reconstruction of canonical source cursors through bodies,
  control flow, calls and returns at every `Evidence.RuntimePoint`.
  Generic parameter-prologue correspondence now preserves incoming caller value and run maps.
- `TH-CON-01` needs separation and byte geometry derived after arbitrary accepted
  initialization, the complete fill loop, and invocation replay through all 23 evaluator families.
- `TH-EXIT-01` needs the accepted owner-to-storage bridge through reservation and landing,
  with outside-root observations preserved. Existing normalized-channel and concrete checks remain components.

These obligations remain open. No exhausted full-acceptance attempt budget is claimed.

Five alternating memory samples pass against baseline `24ba0840` on the same
Aincrad3 input. Median RSS is 1,582,788 KiB baseline and 1,686,388 KiB candidate.
Maximum candidate divided by minimum baseline is 1.0664, below 1.10.
The Release binaries are 5,637,480 and 10,415,648 bytes. No size threshold is specified.
These final memory samples use the reporting fix. Available memory stays above 30.13 GiB.

Five interleaved samples per condition at `02d57ad3` pass readiness checks before
and after every run. CPU seconds below are minimum / median / maximum.

| Command | Baseline, report off | Candidate, report off | Candidate, report on |
| --- | --- | --- | --- |
| `-O2 --check` | 5.198292 / 5.349411 / 5.395433 | 5.602449 / 5.611698 / 6.260169 | 6.637201 / 6.671604 / 7.144562 |
| `-O2 --standalone` | 6.563042 / 6.770916 / 7.069515 | 7.043827 / 7.078505 / 7.386480 | 8.102465 / 8.293610 / 8.611880 |

The 18.9% checking overhead and 17.2% emission overhead exceed the proposed 10% cap.
Reports preserve compiler output and emitted C exactly. Report consistency checks pass.
Report-off checking ranges do not overlap; default checking cost also remains an open
budget question. Emission ranges overlap.
A phase-local node-pool experiment `67e714f4` is rejected and remains unmerged.
Across five interleaved pairs, its median CPU change is 2.1% for checking and 2.3%
for emission, inside the observed spread. Checking ranges overlap at 6.265507–6.850614
versus 6.344176–6.517408 seconds. Emission ranges overlap at 7.740373–8.606291
versus 7.774385–8.202209 seconds. No speedup is claimed.

Cold-build and edit-loop timing series stop when post-run readiness fails.
The corrected edit-loop measurement uses distinct receipt names for each round.
The final attempt stops at E00's post-run check. It supplies no five-sample timing verdict.
**Perf gate deferred: host busy.** Report cost, remaining build-loop budgets,
units runtime and O5 LTO remain unqualified. `G-CLOSE` has not passed.

Resuming performance qualification requires the archived Aincrad3 core entry, the
matching Release baseline, and five alternating valid runs per condition.
Use fresh `GOOSE_HOME` directories for cold builds and one retained directory per edit sequence.
Both build modes need `--standalone` with the two native headers used by the structural matrix.
Timed edit rows omit `--verify-reuse`. Keep report collection separate from frontend
and `native_build` time. Each measured command requires successful default readiness
before launch and `-1` immediately afterward. Discard a sample if either check fails.
The application is not executed by these compiler and build-loop measurements.

Cleanup retires the superseded b72 and 29513 qualification worktrees and the rejected
node-pool worktree, reclaiming about 4.4 GiB of generated artifacts.
The rejected experiment's branch is retained. Qualified v3/v4 artifacts, the immutable
performance baseline, active input fixtures and other parked work remain available.
Nothing is pushed.

## Completion checkpoint (2026-10-25)

The owner requested completion after recovery. The accepted starting revision is `27feef55`.
Local commits remain authorized by the campaign workflow. Pushes remain unauthorized.

Four isolated lanes address construction representation and ownership, exit landing,
source-demand transfer, and the independent Lean audit. Existing endpoint proofs stay intact.
The demand proof uses a separate finite-prefix relation to label actual GIR instructions
with source occurrences and retained slot or SSA values. Construction needs an accepted
runtime representation invariant because its executable syntax is distinct from Core.
These new proof contracts must derive initial validity from validation and preserve it
through actual execution. They cannot assume the whole-run claim they aim to prove.

The production BCE qualification passes again with the recovered compiler and semantic tool.
Four sources emit proven indexes. Three kill controls keep checked indexes.
Forged certificates fail independent validation. `TH-CERT-01` now records both structural
checker soundness and the already-proved reachable-fact theorem.
The units-built linter passes full linter parity and the existing linter suite.
The native reuse matrix passes E00–E16, including interrupted-build recovery;
60 randomized edit steps at seed 1 pass with reuse verification.

The logical checkpoint `a289f963` passes full qualification of 2,643 source modules.
Its fresh native and interpreted audits agree byte-for-byte on 183 unique claims,
using only `Classical.choice`, `Quot.sound`, and `propext`.
All five bundled independent kernels accept both the theorem export and `Main.main`.
The theorem roots have 39,978 dependencies; the runtime root has 16,528.
Their union of 43,870 dependencies is covered by 44,368 exported constants.
The collector checks actual transitive logical dependencies, including opaque bodies
and inductive recursors, rather than every unused constant imported from Lean.
This does not verify native code generation, external implementations, or initializers.
The largest kernel check uses 4,386,066,432 bytes RSS, below the 8 GiB lane budget.

The checked components cover fixed integer-array initializer calls, completion of
already-landed exit channels, and actual-fuel literal-assignment prefixes carrying
incoming operands and runs. Their assumptions and limits are in `semantics/coverage.json`.
They do not establish universal construction ownership or relocation, arbitrary exit
landing geometry, or general demand transfer through calls and control flow.
`TH-CON-01`, `TH-EXIT-01`, and the explicit invariant part of `TH-LOWER-03` remain open.

At this checkpoint the full baseline passes; the legacy units corpus passes 704
programs with zero failures and 50 native-layer or parse-only skips.
Fresh native semantic conformance records 105 pilot agreements, two explicit unsupported
features, three construction agreements, and all nine source trace fixtures in both
numeric profiles and at native O0/O2. The full GIR units corpus exposed additional
production exporter, lowering and cross-unit runtime defects; their repair and rerun
remain required before close.

The Release compiler at this checkpoint passes the same-workload memory gate against
`24ba0840`: five alternating Aincrad3 `-O1 --check` runs give median RSS of
1,585,320 KiB baseline and 1,687,728 KiB candidate. Maximum candidate divided by
minimum baseline is 1.0662, below 1.10. Binary sizes are 5,637,480 and 10,331,008 bytes;
there is no binary-size threshold. Five post-warmup interleaved CPU samples per side,
each bracketed by successful readiness checks, give these results:

| Command | Baseline CPU seconds (min / median / max) | Candidate CPU seconds (min / median / max) |
| --- | --- | --- |
| `-O2 --check` | 5.290299 / 5.424787 / 7.093570 | 5.381467 / 5.597723 / 7.477569 |
| `-O2 --standalone` | 6.392496 / 6.746008 / 9.202553 | 6.749555 / 7.243514 / 8.120179 |

Both sides parse 7,051 declarations in 177 files and check 14,710 specializations.
Emitted C is deterministic within each side and passes Clang syntax checking.
The candidate medians are higher, within the observed spread; no speedup is claimed.
These receipts qualify `a289f963`, not later production fixes. Report-enabled overhead,
quiet production-mode edit-loop timings, units runtime and O5 LTO remain unqualified.
The structural edit matrix's reuse-verification compiles are excluded from timing evidence.
The remaining §11 budgets are not frozen, and `G-CLOSE` has not passed.

The checkpoints below retain earlier recovery history. Their pending-state statements
describe those revisions; this completion checkpoint records the current qualification.

## Recovery checkpoint (2026-10-25)

The former `goose-ir` tip `d440b9ab` predates the October 18 integration work.
Recover the coherent `resume-summary-cpp-qualification` snapshot at `355a8928`,
which includes semantic checkpoint `330a9e17` and the production capacity-summary repair.
Both histories are retained. The existing CI files stay unchanged.
An independent source and history review found the older branch's fixes present in this snapshot.

The Core summary unit, saved GIR reservation unit, and native semantic audit pass on resume.
The audit lists 171 claims with only `propext`, `Classical.choice`, and `Quot.sound`.
All nine construction source fixtures pass exact output, status, and event comparisons.
The resumed compiler and semantic sources match their retained build inputs.
The rebuilt compiler passes the baseline's 678 native cases, 798 JIT cases,
bootstrap, rejection checks, and documentation examples. The struct harness changed during
that run and is rechecked separately through `--only extra/s8_struct_contract`.
These checks do not close the remaining proof gates.

The source repairs on `campaign/lean435` are already incorporated or superseded.
Retain that branch and its worktree for the incomplete paranoid audit.
The [Lean audit handoff](lean-435-paranoid-root-handoff.md) records 456 unqualified root pairs
and the limits of the existing acceptance logs. Preserve its exports and continuation inputs.
The repository pins Lean 4.35.0. The external managed default remains outside this recovery.

Recovery fixes add seven missing expected-output fixtures and restore function origins
to the specified first-variable-or-none rule. The origin regression fails before the fix
and passes afterward. The Core summary and GIR units pass.

The struct harness validates and executes both lowerings against the same exact expected
outcome and stdout. C++ uses direct array-length instructions and reuses slot values,
while Lean emits snapshots. Byte equality between these independent lowerings is not a
qualification claim. Deterministic C++ exports and canonical GIR reencoding remain checked.
Subshells isolate helper variables so nested checks cannot corrupt the fixture's paths or outcome.
The pilot GIR golden now includes the production slot-root annotations.

Cleanup removes 12.66 GB of reproducible binaries and build scratch from the winddown archive.
Source, input packets, results, logs, proof exports, and active worktrees are retained.
The three orphan sibling directories now live under `.work/archive/rfc9/`.
Their BCE and name-cursor fixes are already integrated. Their older typechecker experiments
are superseded. Retained root-owned compiler artifacts could not be removed without elevated access.
The original sibling paths are gone. No branch is deleted and nothing is pushed.

The imported snapshot has 33 pre-existing trailing-whitespace findings.
The recovery edits pass `git diff --check resume-summary-cpp-qualification`.
No formatter runs.

Next delivery: complete the remaining construction and exit execution proofs,
demand-invariant transfer, and paranoid audit before final campaign qualification.
Whole-execution construction and exit proofs, demand-invariant transfer, and paranoid
qualification remain open. Historical source receipts below keep their stated scope.

## Current checkpoint

The last fully qualified C++ construction packet is `d5861339`. Semantic checkpoint `330a9e17` includes full accepted-Core-to-GIR validation and the carried-named-ticket repair. All 2,630 Goose modules plus Main qualify under Lean 4.35; a fresh native executable passes the 171-claim audit. The 41-case model matrix, 328 sanitized native configurations, and nine standard-source fixtures agree exactly. Whole-evaluation ownership and exit proofs, explicit demand-invariant transfer, and paranoid qualification remain open. The production capacity-summary repair passes focused C++ and Lean controls; fresh compiler and resource qualification remain required.

### Evidence by scope

#### Source kernel and transitive audit

The predecessor checkpoint `4f7ccf1a` matched frozen source `dc7cb23b`. Its closure covered 216 changed or new Lean roots since `09374665`, plus `Goose.Audit`, for 1,290 modules. The source-root selection is reproducible from `git diff --diff-filter=AM --name-only 09374665 dc7cb23b -- semantics/Goose`, retaining `.lean` paths present at `dc7cb23b`, converting paths to module names, sorting uniquely, and appending `Goose.Audit`. `verify_closure.py` fully rehashed the resulting dependency closure. The exact expanded command is in `.work/wt/resume-semantic-check-nextplain/.work/tmp/nextplain-command.txt`; its completion log is `nextplain-closure-restart.log`. A separate `Goose.Audit` import reported 171 claims using only `propext`, `Classical.choice`, and `Quot.sound`; its runner and output are `.work/tmp/nextplain-audit.lean` and `.work/tmp/nextplain-audit.jsonl` in that worktree. This predecessor receipt is source elaboration and a transitive declaration audit, not an executable `goose-semantics` build or audit.

The predecessor full-source checkpoint is the region-aligned snapshot `d8b16216daee678d5f766e7665d070cc11e1beab`. From that source tree, derive roots with `git diff --diff-filter=AM --name-only cc063a86 d8b16216 -- semantics/Goose`, retaining `.lean` paths present at `d8b16216`, converting to sorted unique module names, and appending `Goose.Audit`. This produces 144 changed roots plus the audit module. `verify_closure.py` expanded that selection to 1,308 modules and fully rehashed them; the derived module order exactly matches the recorded command. The run reported all 171 registered claims with only `propext`, `Classical.choice`, and `Quot.sound`. Its invocation and result are in `.work/wt/resume-native-regions-aligned/.work/tmp/regions-aligned-check1-resumed.log`. This remains valid source elaboration and transitive audit evidence for `d8b16216`, not qualification for the newer metadata or Core-to-GIR changes.

The newer metadata packet passed its incremental 85-root closure: 310 modules in 311 jobs. Its record is `.work/wt/resume-native-regions-aligned/.work/tmp/regions-aligned-check3.log`. A reviewed branch packet at `d14c85b6` plus controls `842c9e75` repairs a refSlice per-SSA read recipe by adding the actual `.read(.var q)` scope for refSlice variables and preserving aligned raw `Pq` roots. It passed 25 source controls, but source consumers and full Core-to-GIR preservation remain open; the packet is not integrated into `master`.

The proof/source cohort `79aa4f55` changes 80 files, including source-symbol, root-collector, and `ifE` recipe proofs. Follow-up `e1049d9e` integrates 12 proof-only files. Accepted context/global occurrence replay is checked on its proof branch (`35e57a42`, `ccc25cb4`, `2c50671a`, and `7a2bf4d6`); the full cumulative source closure and 171-claim audit remain open for `0463de24`.

The current `Goose.Lower.Validation.lower_validate_of_accepted` theorem proves `Core.validate module = .ok () → GIR.validate (lower module) = .ok ()` for both `core-pilot` and `core-shrink`. It adds no target-validation, callee-simulation, ownership, query-availability or independence premise. The cumulative source qualification passed 2,588 modules under Lean 4.35. The stronger 171-claim interpreted audit passed with only `propext`, `Classical.choice`, and `Quot.sound`. The fresh native executable also passes the stronger 171-claim audit; paranoid qualification remains pending. `TH-LOWER-03` remains deferred for explicit transfer of the per-point demand, retained-operand and iteration-run invariant. The forward, reverse, fault-freedom and converse-fuel claims retain their statements and limits.

The earlier pilot-profile accepted-Core-to-`GIR.validate` theorem closed on branch `17c7a70e`. Its exact source closure covered 1,186 modules in 1,187 jobs under Lean 4.34.1 and used the three standard axioms. The theorem assumes only Core acceptance and the pilot profile; it adds no target-validation, callee-simulation, query-availability, or ownership-certificate premise. That earlier receipt did not close SHRINK validation.

`SourceReady` receipts are profile- and source-specific. Branch `c9dae54e` checked the accepted-only factory and consuming-operand values over 1,129 modules and 1,130 jobs under Lean 4.34.1; model source blob `ffbb0ef` is an older ambient-call model. The current raw-owner model uses `07ad913d` with the actual-step fix `0a62e909`; proof port `621163f7` closed a 124-module source closure, 184 guards, and 311 standard-axiom audits. Those results do not qualify the newer `SourceReady` model. The current cumulative source qualification includes the coherent accepted-only validation endpoint and its source-derived call and writer proofs.

To reproduce a source selection and closure, run from its target checkout and set `base` and `target` to the source pair named above. Use `09374665` and `dc7cb23b` for the predecessor selection instead:

```sh
base=cc063a86
target=d8b16216
mapfile -t roots < <(
    git diff --diff-filter=AM --name-only "$base" "$target" -- semantics/Goose |
    while IFS= read -r path; do
        case "$path" in
            *.lean) git cat-file -e "$target:$path" 2>/dev/null || continue
                   module=${path#semantics/}
                   module=${module%.lean}
                   printf '%s\n' "${module//\//.}" ;;
        esac
    done | sort -u
)
roots+=(Goose.Audit)
module_args=()
for module in "${roots[@]}"; do module_args+=(--module "$module"); done
TMPDIR="$PWD/.work/tmp" python3 test/semantics/verify_closure.py --semantics-root semantics "${module_args[@]}"
```

Three closed lowering results remain valid for the definitions they state. `28eb9cc1` proves forward lowering preservation for accepted Core modules at every source fuel bound. `1da41160` checks reverse execution and all-fuel target-fault exclusion. `770db8aa` proves the converse fuel bound `8 * (moduleSyntaxCap + 1) * (targetFuel + 2) + 1`; its 265-module closure and independent review passed. Neither direction assumes source termination or an owner-shape certificate. These model results do not establish C++ lowering or native-emitter correctness.

#### Fresh executable semantics

The fresh native `goose-semantics` for `330a9e17` passes its actual 171-entry audit, including `lower_validate_of_accepted`, with only `propext`, `Classical.choice`, and `Quot.sound`. All 2,630 Goose sources plus Main qualify: 149 modules were rebuilt and 2,482 artifacts reused only after source and recursive-import identity checks. The native executable covers 2,014 modules, with five rebuilt objects and 2,009 objects reused after source, import, and package-initializer identity checks. All artifacts are regular private files. Results and the executable are under `resume-repaired-model-integration/.work/tmp/` (`source-qualification.log`, `native-build.log`, `native-audit.log`, `native-matrix.log`, and `native-current/goose-semantics`).

The executable passes 328 exact comparisons over 41 cases and both numeric profiles, including Core/GIR execution, writer roundtrips, and agreement checks. The unchanged `d5861339` production compiler passes 328 ASan/UBSan configurations and the nine-fixture source CLI trace suite against this fresh oracle, including rejection and trace-I/O controls. All 82 fresh C++ Core/GIR exports are byte-identical to the tested packet inputs. Canonical Lean Writer output has one fewer terminal newline; no input or observable event was normalized. Case 41 at equal fuel 30 remains inconclusive because the evaluators count different work.

The permanent argument-renewal and carried-named-ticket regressions pass the fresh CLI in both profiles. The carried-ticket fixture faults with `flow` in the frozen `8d2137f6` executable and now returns `AB\n` with exact events `begin 0, begin 1, write 1 0, write 0 0, publish 0, publish 1`. Its exact nested value-break form is unsupported by the source frontend. A C++ Core builder reproduces its original wire module exactly, but direct GIR lowering rejects its unknown summary. Running the real production summarizer produces independently accepted GIR whose model and eight sanitized native configurations agree with the accepted original Core. At `d5861339`, that summarized Core is rejected with `V-SUMMARY` because receiving-capacity uncertainty was omitted from its abort effect. A production summarizer fix is under review; no validator relaxation is proposed.

The older executable and results under `resume-candidate-integration/.work/tmp/native-current/` remain historical evidence for `8d2137f6`.

Full paranoid qualification remains incomplete. Monolithic nanoda checks exceeded the guarded memory budget; dependency-closed official exports bound the check size. An external lean4lean replay-context bug required splitting one export and adding checked Init context while retaining every original root. Its split groups now pass all bundled kernels; remaining groups are pending. No checker or axiom allowlist was changed. The default Lean remains 4.34 until qualification finishes.

#### Integrated C++ candidate

The current packet `d5861339` integrates limited receiving construction, staged storage, and private cursor validation. Review found that `LocalGet` and `LocalSet` could bypass cursor protection. Both now reject private inline cursor members with `GIR-V090`, with negative controls that accepted before the fix. All three focused GIR units pass on the integrated commit. The candidate also passed a fresh serial Debug build, both GIR source scripts, and four numeric and optimization configurations of 56 sanitized receiving-lifetime guards. Those checks do not establish the remaining semantic or performance gates.

Fresh exports from this packet passed 82 independent Core/GIR comparisons across 41 cases and both numeric profiles at sufficient fuel. All 328 ASan/UBSan native configurations matched exact status, stdout, diagnostics, and construction events. The nine standard-source fixtures also passed fresh CLI and semantic comparisons, including trace I/O controls. These comparisons used an explicit Lean 4.35 Main runner; they do not establish a fresh native semantic executable for the combined proof candidate. The runners and results are under `resume-cpp-integration/.work/tmp` (`run-native328-current.py`, `native328-current`, and `cpp-current-packet`).

The checked candidate `a26a9783` is the source base for the six C++ commits now integrated at `153f44f0`. A Git comparison confirmed that `src`, `test`, the GIR specification, and native construction contract files are byte-identical between them. From `resume-cpp-closing`, all three focused GIR units passed:

```sh
TMPDIR="$PWD/.work/tmp" clang++ -std=c++20 -O0 test/compiler_gir.cpp -pthread -lm -o .work/tmp/compiler_gir-closing && .work/tmp/compiler_gir-closing
TMPDIR="$PWD/.work/tmp" clang++ -std=c++20 -O0 test/compiler_gir_effects.cpp -pthread -lm -o .work/tmp/compiler_gir_effects-closing && .work/tmp/compiler_gir_effects-closing
TMPDIR="$PWD/.work/tmp" clang++ -std=c++20 -O0 test/compiler_gir_reservations.cpp -pthread -lm -o .work/tmp/compiler_gir_reservations-closing && .work/tmp/compiler_gir_reservations-closing
```

A fresh Debug GCC `goose` build also passed on the candidate:

```sh
TMPDIR="$PWD/.work/tmp" cmake -S . -B .work/build-cpp-closing -DCMAKE_BUILD_TYPE=Debug
TMPDIR="$PWD/.work/tmp" cmake --build .work/build-cpp-closing --target goose --parallel 2
```

The resulting `.work/build-cpp-closing/goose` passed four selected baseline fixtures (eight parse/roundtrip/typecheck checks, four generated-C `-O0`/`-O2` runs, and four TinyCC runs):

```sh
TMPDIR="$PWD/.work/tmp" python3 test/run_tests.py --exe .work/build-cpp-closing/goose --profile baseline --cc native --jobs 1 --batch 1 --only storage/relative_known_null --only storage/relative_store_facts --only storage/pool_reference_rebinds --only codegen/named_fn_value_scope
```

Both GIR source scripts passed:

```sh
TMPDIR="$PWD/.work/tmp" sh test/gir/source/check.sh .work/build-cpp-closing/goose
TMPDIR="$PWD/.work/tmp" sh test/gir/source/check_regressions.sh .work/build-cpp-closing/goose
```

The source fixture was `.work/tmp/cpp-closing-source/conditional_reference.goose`. Its Core, high GIR, and low GIR exports passed parsing, typechecking, and lowering; the high GIR included the expected `er` source-root row, verified by `jaq`:

```sh
.work/build-cpp-closing/goose -O0 --pipeline gir --emit-core .work/tmp/cpp-closing-source/conditional_reference.core.json --emit-gir-high .work/tmp/cpp-closing-source/conditional_reference.high.json --emit-gir-low .work/tmp/cpp-closing-source/conditional_reference.low.json --check .work/tmp/cpp-closing-source/conditional_reference.goose
jaq -e '.[6][] | select(.[0] == "func" and .[1] == "pick") | .[7][5] == [["er",9,[["r_param",0],["r_param",1]]]]' .work/tmp/cpp-closing-source/conditional_reference.high.json
```

These are bounded candidate checks, not a fresh semantic Main build, source9 comparison, full source corpus, or completed Core-to-GIR theorem. No stdout/stderr log files were captured for these commands; the export artifacts and GIR script scratch outputs remain under `.work/tmp` in the candidate worktree.

Later commits `a6fa5be8`, `058a1b9f`, and `bff0b04e` on `campaign/cpp-closing` passed the three focused GIR units and a fresh Debug build. They are not integrated into `master`, and no source9 trace was run on this candidate. Its source exports still lack support for reference-to-slice and shrink-demand forms.

The newer bounded C++ candidate `563e0b7a` on `campaign/call-transport-policy` passed a serial Debug build, all three focused GIR units, both GIR source scripts, and nine baseline fixtures. Its binary is 64,618,240 bytes. The sampled process-tree RSS was 4,030,796 KiB during the build and 276,476 KiB during the forced link-only run. The sample is not a peak or a hard memory bound. The candidate has no fresh Main build or full source differential; 17 pre-existing indentation warnings remain.

#### Construction Core, GIR, and native execution

The bounded construction packet combines native freeze `f8bbed7c`, high-GIR commits `4abec5a3` and `2dac55da`, independent high-GIR freeze `4e5d1c65`, and exact Core source `d03511ca`. It predates the later limited Stage/Fit helpers and is not evidence for current 61-control coverage or an integrated `master` Main build. Its earlier 224-configuration native matrix is a separate historical receipt: it checked hard-coded stdout, status, and event expectations, not Core or Main parity.

The fresh Core probe decoded and validated 35 selected fixtures, then ran each in both numeric profiles at fuel 10,000. It recorded stdout, status, and encoded events. The comparison requires exact event equality, including semantic destination and storage identities; it does not rename identities or compare physical addresses as identities. From `resume-construction-ownership`, the command was `TMPDIR="$PWD/.work/tmp" LEAN_PATH="$PWD/semantics/.lake/build/lib/lean" /home/josh/.local/lib/lean4/v4.34.1/bin/lean -j1 -M4096 .work/tmp/rearm-final-35-core-probe.lean > .work/tmp/rearm-final-35-core-probe.log 2>&1`. The source and result are `rearm-final-35-core-probe.lean` and `.log`. The fixtures are the 35 `*.core.json` files under `resume-native-trace/.work/tmp/interrupted-native/rearm-frozen-packet`.

The independent GIR-H check decoded, validated, and wrote back all 35 fixtures, then compared 70 release/debug executions with Core. Its case list and result are in `finish-construct-gir/.work/tmp/gir-current35-corpus.log`. The native selector is `test/compiler_gir_reservations.cpp`. The combined oracle comparison ran all 280 sanitized C executions against Core stdout, status, and trace events. The exact command was `TMPDIR="$PWD/.work/tmp" python3 .work/tmp/interrupted-native/compare-rearm-fresh-oracle.py` from `resume-native-trace`. The 248, 16, and 16 configuration records are in `rearm-final-matrix.log`, `rearm-named-matrix.log`, and `rearm-child-matrix.log`. The 280 generated C files and runtime headers matched the final emitter in `rearm-frozen-bytecompare.log`.

The pre-rearm 224-run matrix is historical and uses fixed expected outputs and event arrays rather than Core or Main as an oracle. Its selector is the 28-case loop in `test/compiler_gir_reservations.cpp` at `1bde5daa`: `break`, `continue`, `call`, `named-borrow`, `owner-child`, `owner-named`, `cross-same`, `cross-different`, `deferred-cleanup`, `own-deferred-cleanup`, `value-break-cleanup`, `nested-break`, `nested-continue`, `waiting-implicit`, `waiting-explicit`, `waiting-nested-return`, `waiting-stop`, `waiting-built-before-tail`, `waiting-own-catch`, `waiting-guarded-call`, `waiting-delegated-argument`, `waiting-guarded-argument`, `adapted-open`, `adapted-built`, `adapted-nested`, `named-layout-result`, `named-layout-nested-read`, and `named-layout-helper-read`. Each case ran with debug off/on, `-O0`/`-O2`, and plain/traced output (28×2×2×2); C was compiled with AddressSanitizer and UndefinedBehaviorSanitizer. The saved runner and matrix log are `.work/tmp/interrupted-native/check-adaptation-final-matrix.py` and `adaptation-final-matrix.log` in `resume-native-trace`; the log records 224 exact rows, and the runner checks hard-coded output, status, and trace arrays. A rebuild can be reconstructed at that source with `clang++ -std=c++20 -O0 test/compiler_gir_reservations.cpp -pthread -lm -o .work/tmp/utility`; this is not the recovered original emitter build command, and no source identity for the historical utility binary was retained. The separate nine-fixture source comparison covers 36 runs and is not part of the 224 matrix.

The four-profile native receiving-lifetime guards passed in `rearm-frozen-lifetimes.log`, run with `python3 test/semantics/native_receiving_lifetimes.py --emitter .work/tmp/interrupted-native/rearm-frozen-utility --sanitize`. The unsanitized nine-fixture Debug/release source comparison passed 36 `-O0`/`-O2` runs plus CLI and I/O controls. The command used `python3 test/semantics/native_construction_trace.py --goose .work/tmp/interrupted-native/driver-build/goose --semantics /home/josh/d/goose/.work/wt/resume-audit/semantics/.lake/build/bin/goose-semantics --cc clang`; its result is `rearm-frozen-source9.log`. These bounded receipts do not establish same-checkpoint parity with integrated `master` or a fresh Main build.

Named-value sampling allocates no storage. A reference call retains one two-pointer `owner_ref` record per distinct binding in that callee scope; repeated samples reuse the record. That is 16 bytes on a 64-bit target, as described in the [native construction contract](goose-ir-construction-native.md). This is a representation fact, not a performance result.

The fixed-array call evaluator repair is frozen on branch commits `69d7c1b0`, `0520a903`, and `f3a8e96f`, not integrated into `master`. The first commit passed a strict 21-module, 22-job closure and eight standard-axiom audits. Its direct fit and overflow checks show that a known fixed call avoids staging; overflow prints `effect\n`, emits no construction events, and leaves the prior storage sentinel unchanged. Unknown variable-array calls still stage. The second commit passed a strict 22-module, 23-job closure and twelve standard-axiom audits. Accepted Core and native exports agree in both profiles: dead fixed/live variable-array results print `ABC\n` and stage, while dead variable-array/live fixed results print `AB\n` without staging. The direct fixed-call fit prints `effect\nAB\n`; its overflow prints `effect\n` and has a capacity abort at origin 0 with no events.

A nested recursive-query bug was reproduced in the same branch. In a `view.val` with a dead `arr2` branch and a live `arr3` branch, the typechecker derives `arr3` but the recursive declaration query picks `arr2`. Before the fix, evaluation for a limited capacity of two printed `effect\n` and emitted begin plus two writes before a capacity abort at origin 0; the expected overflow emits no construction events. Branch commit `f3a8e96f` fixes the query; `cd0174e9` adds the no-tail value-break overflow and fixed-source inversion cases. That 40-case Core corpus passed decode, validation, and evaluation in both profiles. Its canonical trace comparison was still pending at that checkpoint. The later canonical comparison passed for 40 cases in `.work/tmp/construction-delivery-8ce-canonical40`. The current native comparison and the separate case-41 GIR mismatch are described below. No integrated Main is established. Full `C-DIRECT` and `C-STAGE` still require query agreement, original-capacity-layout, renewal, and accepted inline-result proofs.

The limited construction Stage/Fit tranche is branch-only. It adds `l_control_attempt_stage` and `l_control_attempt_fit`, bringing the closed low inventory to 61. The high validator permits Stage after a ticket, but native support is limited to a fresh, unexposed `Open0` attempt. Canonical Stage trace JSON remains `["stage", id, "capacity-check"]`. The prior 40-case GIR and 320 sanitized native comparisons predate the private-cursor guard and are historical. The fresh native run passed all 328 ASan/UBSan comparisons against the canonical Core output, with Core/H inputs and emitted C/runtime byte bindings checked. The 39 cursor controls and four 56-case receiving-lifetime suites passed. Logs are under `.work/wt/accelerate-native-current/.work/tmp/native-current/` (`matrix.log`, `lifetimes.log`, and `controls.log`).

The independent GIR rerun in `accelerate-gir-parity` decoded, validated, and re-encoded all 41 records and matched their exact Core outcomes, stdout, and construction events in both profiles at fuel 100000. Its receipt is `.work/tmp/construction-gir-canonical41-sufficient-fuel.log`: exit 0 and 82 profile matches. Case 41 also matches at GIR fuel 32. At fuel 30, Core returns `effect\nA\n`, while GIR times out after `effect\n` with the same begin/write/publish events. These evaluators count different work. `TH-LOWER-01` permits a corresponding target fuel bound, and the existing `agree` command treats either-side timeout as inconclusive. The earlier scratch runner's equal-fuel assertion exceeded that contract. No interpreter fuel accounting or event normalization changed. These checks use the pending construction overlay in that worktree; they do not qualify integrated `master` or a fresh Main executable. The low-fuel Core query regression remains a separate required check.

#### Resource and performance

The current C++ packet `d5861339` passes the same-workload compiler-memory gate against `24ba0840`. Both use serial Clang 23.1.3 Release builds and the same Aincrad3 `src/world-core-continue.goose -O1 --check` input. Five alternating runs per side completed successfully with identical diagnostics and work counts within each side. Baseline ru_maxrss ranges from 1,580,352 to 1,586,480 KiB (median 1,582,700); candidate ranges from 1,683,756 to 1,687,104 KiB (median 1,686,348). Even maximum candidate divided by minimum baseline is 1.0675, below the 1.10 limit. Process traces confirmed no child processes, so these are hard compiler-process peaks. The run maintained the 18 GiB available-memory guard. Release binaries are 5,637,480 and 10,447,824 bytes; no binary-size threshold is defined. The gated CPU comparison follows below. The runner and individual reports are under `.work/tmp/cpp-current-resource/`.

Five alternating Release runs per side passed readiness checks immediately before and after each CPU measurement. Both commands use the same Aincrad3 source at `-O2`, with report collection disabled. Every run parsed 7,051 declarations from 177 files and checked 14,710 specializations. Emitted C was stable within each side and passed Clang syntax checking outside the timed region.

| Command | Baseline CPU seconds (min / median / max) | Candidate CPU seconds (min / median / max) |
| --- | --- | --- |
| `--check` | 4.814217 / 4.841570 / 5.371013 | 5.091032 / 5.160924 / 5.902769 |
| `--standalone` emission | 6.024175 / 6.240335 / 6.735160 | 6.397680 / 6.481692 / 6.871062 |

Candidate medians are 6.6% and 3.9% higher. The differences between minima are smaller than the observed run spreads, so neither fails the prescribed spread-based gate. Separate profiling attributes most sampled CPU to typechecking and bounds-check elimination. Emitted C sizes are 67,085,728 baseline and 65,262,980 candidate bytes. The measurement runner and individual readiness/compiler outputs are under `.work/tmp/cpp-current-resource/` (`cpu_gate.py` and `cpu-samples.tsv`).

Two sampled process-tree cases measured the predecessor's warm 1,290-module closure at about 1.09 GiB and an existing serial compiler fixture at about 1.52 GiB. The samples and sampler are `nextplain-rss-warm.log`, `verifier-rss-real-inputs.log`, and `sample-verifier-rss.py` in `resume-semantic-check-nextplain/.work/tmp`. These predecessor observations do not qualify the current sources.

Matched serial Debug builds with Clang 23.1.3 and `-g` succeeded for baseline `24ba0840` and candidate `563e0b7a`. The baseline binary is 25,671,216 bytes; its sampled process-tree RSS maximum was 963,640 KiB. The candidate binary is 56,836,592 bytes; its sampled maximum was 1,968,664 KiB. Both builds used `cmake --build .work/build-perf-debug --target goose --parallel 1`. Their logs are `.work/tmp/baseline-debug-build.out` and `.work/tmp/candidate-debug-build.out` in `accelerate-perf-baseline` and `accelerate-perf-candidate`, respectively. The sampler checks descendants every 50 ms, can miss intervening peaks, and can count shared pages twice. These are full-build resource observations, not hard memory bounds or an isolated regression measurement. The incremental-memory gate remains unrun. No timing result qualifies; timing gates await the required semantic and executable qualification.

#### Remaining proof obligations

Full accepted-Core-to-GIR validation is proved for both artifact profiles. The actual-call owner-alias repair propagates possible owner aliases from call arguments through contexts, global initializers and recursive forwarding. `V-WHOLE` and `C-NOGROW` validation use those aliases. Name-only roots propagate independently of effects. The repair rejects the same-owner clear-before-copy regression while preserving harmless aliased reads and copies between distinct owners. This closes the validator bug. The whole-evaluation `C-NOGROW` ownership theorem remains open.

The replacement-content-flow model uses the callee's actual touched roots at a call. Forwarding an argument alone no longer adds it to the caller's exported touch footprint. Call queries still include argument dependencies and callee accesses. Virtual slice contents and assigned writes remain in the analysis. `ReplacementCallForwardingChecks.lean` covers accepted pure forwarding, rejection of actual owner sampling, and contents propagation.

The `V050` refSlice recipe repair and raw owner-dependency refinements are included in the qualified source packet. Actual source occurrences, seeded provenance, normalized queries, call footprints and lexical writer intervals now compose into the full accepted validation theorem. Explicit transfer of Core's demand and retained-operand invariant to GIR execution remains open. The remaining construction obligations include:

- Preserve fixed-inline result representation kinds through actual evaluation. The observed gap is in the model; no direct C++ regression is confirmed.
- Complete `C-DIRECT` and `C-STAGE` proofs for fixed-inline result representation and fixed-array calls. The evaluator repair is frozen through branch commit `f3a8e96f`, but query agreement, capacity-layout, renewal, and accepted inline-result obligations remain open.

The actual initial `runModule` cannot return an unhandled nonlocal escape: `runModule_no_unhandled_nonlocal` has no acceptance or certificate premise. Its source descent covers all invocation cases and the 53 statement/loop/push/global sites. The focused 105-module closure passes Lean 4.35 at default limits; 158 public theorem audits and two projection-definition audits use only the three standard axioms. This excludes unhandled escape, without establishing successful landing or outside-root preservation.

Rooted `returnFrom` and `returnFromForward` proofs identify the nearest entered handler after normal operands and distinguish an operand's own escape. Native cleanup frames preserve post-operand stdout and object bindings across all outcomes; lexical scope release preserves reads of surviving roots. Their 113-module Lean 4.35 closure and 32 public axiom audits pass. These are execution components; storage preservation and successful landing remain open.

`Goose.Proofs.ExitExecution.argumentReceivingRenewal` preserves an accepted regression in which a normally returning argument writes and abandons the prepared output, then the call renews it and returns `[9]`. Acceptance, exact output/events, and abandoned/resumable/published destination states pass Lean 4.35 with the three standard axioms. The exported Core packet also matches in both numeric profiles through the qualified executable. Production source parity is unsupported for this additional case: the exact while/value-break form is rejected, and the loop-expression alternative is unsupported by the GIR pipeline. An accepted substitute has different events and does not qualify the case. Normal argument evaluation cannot be assumed to leave its output untouched.

An accepted nested two-result regression exposed borrowed cleanup rearming a ready ticket while its exact `pendingNamed` carrier remained live. The repaired evaluator preserves that ticket until owning completion materializes it; unused ready marks still rearm on ordinary break and continue. The actual full program now returns `AB\n` with the expected construction events. The repaired 119-module closure and 57 declaration audits pass Lean 4.35 at default limits with only the standard axioms. This preserves the existing protocol rather than allowing an invalidated named handoff in the proof contract.

The whole-evaluation `TH-CON` and `TH-EXIT` proofs remain open. Existing lifecycle, token, destination, and receiving-boundary lemmas are components, not whole execution proofs. The remaining work includes positive-fuel source induction and accepted `runModule`, reservation `SourceState` preservation through renew/reserve/select/cancel/materialize/restore, actual receiving-boundary and ownership transport, protected-prefix geometry and byte-frame behavior, and extraction of the seven construction rules plus post-operand `TH-EXIT`.

The proof boundary excludes correctness of the C++ frontend/exporter, C++ emitter, C compiler or linker, and operating system. See the [trust ledger](../../semantics/trust.md).

## Historical handoff (2026-10-14; superseded)

The handoff below describes the paused 2026-10-14 snapshot. Its branch inventory, worktree state, commands, and next steps are historical and do not describe the current checkpoint.

**Resume:** "Resume the paused Goose IR campaign from docs/design/goose-ir-campaign.md. Finish the remaining gates unattended. Take recommended decisions by default." First run `git status --short --branch`. On an authorized resume, cancel campaign closeout before selecting work. Recreate a missing selected worktree under `.work/wt` from its named branch.

**State at pause:** The integration branch is `master`. The code checkpoint before this handoff is `a9d3c620`. Winddown started at `dffdf0c2` after the completed integration checkpoint `66b8cdcc`. No work is pushed.

This winddown integrated accepted callee sources, actual global-initializer and entry frames, and the typed block constructor. It also integrated source-versus-receiver exit ownership, exact producer counts, explicit receiving adaptation, producer normalization, and checked allocation and trace-prefix kernel frames. Four positive lowering fixture records now use recognized origin kinds. Their programs, assertions and source lines are unchanged.

The independent Core judgment now proves `validate m = .ok () → WellFormed m`, including unconditional origin validity. Adversarial review found no P1 or P2 defect. Its Audit registration and coverage entry were integrated on resume in `f6ef88c6`. The fresh executable audit from `432c7d19` passed all 158 registered claims with the three allowed axioms. A final audit after the active proof changes remains open. The universal BCE replacement proof is merged. The last full executable audit checked 157 claims at `9e888683`; no fresh full audit of the current code is claimed.

**Known red:** Whole-profile lowering and validation preservation remain incomplete. The unmerged readonly-destination change `920c9e42` invalidates unrestricted legacy fragment claims. Replace those claims with accepted-state composition before integration. The construction whole-execution and exit gates remain incomplete.

At `66b8cdcc`, raw-byte high GIR rejects with `GIR-V060`. The source-values high GIR executes correctly but re-encoding changes its declared type table. Native exports of raw bytes and source values fail `GIR-V090` stack-header ownership. Source-exit high export fails return-descriptor matching. These source fixtures are committed at `test/semantics/golden/construction_raw_bytes.goose`, `test/semantics/sem_construction_source_values.goose`, and `test/semantics/sem_construction_source_exit.goose`. The paused branch does not claim these integration failures are fixed.

Production BCE qualification is also red. The seven fixtures on `goose-ir-finish-bce` export and independently validate, but the required guarded case emits zero proven indexes. Read that branch's `docs/design/goose-ir-bce-qualification.md` before changing certificate rules. H2 structural requalification passed at `c1070ef0`; §11.3 records its scope. Final performance measurements and campaign-wide gates have not run. O2 remains unadmitted, and the earlier O3 timing was invalidated.

**Standing decisions:** The owner accepts recommended decisions by default. E10 qualifies the production builder boundary for independent C flags, target identity and runtime identity. Construction-only struct descriptors carry display names. Repeat-copy and operand-time byte snapshots are explicit operations. Array, fill, if and block records carry source origins. The third native result pointer addresses `{count, destination_id}` as two i64 fields. Pilot and shrink wire records remain unchanged.

Recommended construction-only publication, adapter, provenance and target operations are approved. The parked implementation uses `i_dest_publish_ref`, `i_dest_adapt` and `i_dest_adapt_finish`. Adapter finish preserves the built or cancelled kind and restores the original receiving metadata. Document exact wire operands and native target operations before integrating those unfinished changes. No owner decision is pending.

**Open lanes:** The owner accelerated the campaign on 2026-10-17. Accepted-state lowering, validation preservation, generic expression SSA typing, native construction handlers, construction execution proofs, production BCE, H2 closeout, exact-module verification tooling, and independent construction GIR review have separate owners. The Core audit registration and H2 probe repairs are integrated. Construction GIR wire checks are committed and under independent review. The paused inventory below records their starting branches. Incomplete working edits were committed on their lane branches before stopping. The table below names all 37 unmerged local branches. Eleven are current campaign lanes or the performance baseline. Twenty-six are owner-managed refs. A different branch history does not prove its patch is missing from master. Review specific file deltas and dependencies.

| Unmerged branch | Tip | Item | State | Next step after resume |
|---|---|---|---|---|
| `backup/master-before-upstream-20261010` | `3a25b43c` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `bookkeeping/gs-003-diverging-dead-code/base` | `6417b91e` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `bookkeeping/gs-004-default-init-order/base` | `3a25b43c` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `experiment/emitted-body-diagnostics` | `6be31c0c` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `feat-semantic-linter` | `6d538382` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `fix/codegen-local-name-cursor-rfc9-fork` | `54f1a765` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `fix/gs-002-callee-local-provenance` | `cd00459d` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `fix/gs-003-diverging-dead-code` | `3a25b43c` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `fix/gs-004-default-init-order` | `4a2c8bf5` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `fix/lint-facts-limit-512mib` | `0c127337` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `fix/lint-root-depthkey-context` | `6be31c0c` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `fuzzygoose` | `592aee41` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `goose-ir` | `d440b9ab` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `goose-ir-finish-bce` | `a1b1ed32` | G-BCE | parked: universal model proof merged. Qualification tests82e9fa82 and a1b1ed32 unmerged | Read the branch qualification document. Production pilot sources emit no proven index because snapshots use i_vlen while F-LEN requires i_alen. |
| `goose-ir-finish-construct-backend` | `dcdc9227` | S9, G-CONSTRUCT | parked: low target handlers and provenance remain unfinished in dcdc9227 | Check compiler_gir, then reproduce the three committed construction source fixtures. Complete target handlers before claiming native qualification. |
| `goose-ir-finish-construct-core` | `1a45de91` | TH-CON-01, TH-EXIT-01 | parked: checked kernel stages through 678fd9c2 merged. Additional destination proof snapshot 1a45de91 is unverified | Review only the final destination proof delta. Compose it with the evaluator and whole-execution proofs. |
| `goose-ir-finish-construct-execution-proofs` | `62fcd00b` | TH-CON-01, TH-EXIT-01 | parked: execution-prefix and terminal-state proof stages plus unfinished mutual invariant in 62fcd00b | Build ConstructionExecutionChecks and ExitExecutionChecks against the current shared kernel. Finish fresh-activation and trace protocol closure. |
| `goose-ir-finish-construct-gir` | `53c0c738` | S9, G-CONSTRUCT | parked: borrowed publication and explicit adapters in 53c0c738 require checking | Check independent GIR syntax, writer, verifier, interpreter and guards together. Reproduce raw-byte V060 and type-table roundtrip. |
| `goose-ir-finish-lower` | `631e1665` | TH-LOWER-01, TH-LOWER-03 | parked: readonly destination migration920c9e42 and canonical families. MutationStatements snapshot 631e1665 unfinished | Review typed closure and replace false unrestricted legacy claims before integrating920c9e42. Compose the accepted-state mutual induction. |
| `goose-ir-finish-lower-call` | `dad0c5e3` | TH-LOWER-01, TH-LOWER-03 | parked: full TypedExpressionFamily through dad0c5e3 awaiting coherent lowering integration | Use smaller accepted-source block callbacks. Integrate with the main typed statement and function family, not an assumed whole-call simulation. |
| `goose-ir-finish-lower-each` | `ff5320f4` | TH-LOWER-01, TH-LOWER-03 | parked: canonical foreach stages through ff5320f4 await the typed statement family | Review the canonical foreach commits ending ff5320f4. Derive live owner shape from accepted execution, not a body simulation premise. |
| `goose-ir-finish-lower-source-contexts` | `9174eac7` | TH-LOWER-01, TH-LOWER-03 | parked: startup through a6b6124b merged. Child-source stages444c4849 through 9174eac7 await typed-family integration | Compare helpers with the caller requirements and integrate the missing child-source stages in order. |
| `goose-ir-finish-lower-validation` | `0c91823e` | TH-LOWER-02, TH-LOWER-03 | parked: validation stages through 0c91823e depend on readonly destination migration | Integrate only after 920c9e42 and typed legacy replacements. Finish whole-module typing, dominance, scope, storage and lifetime preservation. |
| `goose-ir-finish-perf-base` | `24ba0840` | O3, final performance gates | parked baseline: upstream46356c26 plus matching runtime stack correction24ba0840 | Keep baseline flags aligned. Measure only after perf-gate-ready succeeds before and after each timed run. |
| `goose-ir-parity-base` | `011acacf` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `goose-ir-view-source-only` | `733bfc0c` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `integrate/upstream-20261010` | `c01d8f9d` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `perf/rfc9-bce-upstream-qualification` | `23366273` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `qualify/upstream-fee060c-20261011` | `ad8f2a87` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `review/cached-callee-references` | `925d52bb` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `review/pr18-latest` | `a3556c11` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `review/reordered-reference-fields` | `865b1aa6` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `upstream-pr/cached-callee-references` | `298bd817` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `upstream-pr/gs-004-reordered-reference-initializers` | `81004d20` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `upstream-pr/native-package-rebuild-stamp` | `8a3637b1` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `upstream-pr/native-stack-bounds-main-thread-musl` | `7cd75268` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |
| `upstream-pr/reordered-reference-fields` | `d68e4427` | owner-managed ref | parked: no campaign item scheduled | Preserve this ref. Review independently before reuse or deletion. |

**Retained worktrees:** All registered worktrees are under the repository. The nine retained trees below are clean and allowed by the closeout guard. Their caches are disposable. Their sources and findings are committed, so none is required after reboot.

| Path | Branch | HEAD | Status | Reason |
|---|---|---|---|---|
| `.work/wt/finish-construct-backend` | `goose-ir-finish-construct-backend` | `dcdc9227` | clean | Incremental C++ compiler and GIR test artifacts for unfinished handler work. |
| `.work/wt/finish-construct-execution-proofs` | `goose-ir-finish-construct-execution-proofs` | `62fcd00b` | clean | Incremental Lean dependency cache for the named parked proof lane. |
| `.work/wt/finish-construct-gir` | `goose-ir-finish-construct-gir` | `53c0c738` | clean | Incremental Lean dependency cache for the named parked proof lane. |
| `.work/wt/finish-lower` | `goose-ir-finish-lower` | `631e1665` | clean | Incremental Lean dependency cache for the named parked proof lane. |
| `.work/wt/finish-lower-call` | `goose-ir-finish-lower-call` | `dad0c5e3` | clean | Incremental Lean dependency cache for the named parked proof lane. |
| `.work/wt/finish-lower-validation` | `goose-ir-finish-lower-validation` | `0c91823e` | clean | Incremental Lean dependency cache for the named parked proof lane. |
| `.work/wt/finish-perf-base` | `goose-ir-finish-perf-base` | `24ba0840` | clean | Matched baseline sources and release artifact. Timing remains unqualified. |
| `.work/wt/verify` | `detached` | `a9d3c620` | clean | Exact merged Core and lowering dependency cache. Expensive single-thread proof builds are reusable only for equivalent sources. |
| `.work/wt/verify-construct` | `detached` | `c4d51371` | clean | Checked construction kernel and exit dependency cache. |

**Cleanup:** Twenty-five integrated branch refs were deleted after ancestry or complete patch-equivalence checks. Forty-three tags preserve frozen experiments and retired candidate histories. Completed and obsolete campaign trees were removed. Six dirty sibling experiments were archived before checkout removal. Their snapshots now use local archive tags. Their original named refs were unchanged. The archive commits retain detached baseline tips too. Two unregistered partial directories remain because root-owned generated files blocked deletion. `../goose-rfc9-gig-perf-20261011` remains unregistered and untouched. Read [the cleanup record](goose-ir-winddown-cleanup.md) for their paths and archive refs. No registered external worktree remains.

**Not started:** On resume, first check the parked code against the current shared interfaces. Complete accepted-state lowering and validation preservation. Complete independent construction GIR, native target handlers and the whole-execution proofs. Then qualify production BCE and rerun H2. Finish the required baseline, linter, JIT, corpus and bounded fuzz gates. Run the final axiom audit and quiet-host performance comparison last. Pushes remain unauthorized.

**Verified:** At `08567a89`, sequential selected Lake closures passed 76 modules for source-context and typed-block checks and 19 modules for the first exit/kernel slice. At `c4d51371`, the construction closure passed 39 modules, including 50 destination guards, 80 execution guards, 47 typing guards and the combined typing/runtime proof. At `a9d3c620`, the fixture closure passed 95 modules for TypedExpressionChecks and CallChecks. Lake used actual `-j1 -M4096` Lean flags. Six new exit/allocation theorem audits use only `propext`, `Classical.choice` and `Quot.sound`. Units-matrix tests pass 14 cases. The semantic runner self-test passes 30 cases. Whitespace checks pass.

The main checkout and all retained trees were checked for uncommitted files. Worktree pruning completed. `.work` is ignored through `.git/info/exclude` and is on ext4. No Lean, Lake, compiler, build, fuzz or watcher process remains from this campaign. No campaign wakeup is scheduled through the available tool interface. User crontab inspection reports no crontab. Privileged root-cron inspection was denied; `atq` and `systemctl` are unavailable.

The Codex Stop command is `"$HOME/.local/bin/codex-campaign-closeout.py" hook`. Its trusted configuration was reviewed. This API session cannot invoke interactive `/hooks`; the configured command was checked directly. The configured command was exercised during winddown. All nine retained trees are allowed. Interactive hook UI verification remains unavailable.

**Rehearse resume:** Run this inspection block in a clean environment. It starts no lane and performs no build. On a real resume, follow the standing decisions and the next steps above.

```sh
set -eu
cd /home/josh/d/goose
git status --short --branch
git log -5 --oneline master
git merge-base --is-ancestor 46356c26a94f0e1723b3b61ad56b93a7da70878f master
git worktree list
git branch --no-merged master
sed -n '1,260p' docs/design/goose-ir-campaign.md
for branch in $(git for-each-ref --no-merged=master --format='%(refname:short)' refs/heads); do
    git show --no-patch --format='%h %s' "$branch"
done
for path in docs/design/goose-ir-spec.md docs/design/goose-ir-validation.md docs/design/goose-ir-winddown-cleanup.md docs/development.md docs/testing.md semantics/coverage.json semantics/decisions.md semantics/trust.md; do
    git show "master:$path" >/dev/null
done
git show goose-ir-finish-bce:docs/design/goose-ir-bce-qualification.md >/dev/null
git show goose-ir-finish-lower:semantics/Goose/Lower/MutationStatements.lean >/dev/null
git show goose-ir-finish-construct-execution-proofs:semantics/Goose/Proofs/ConstructionExecution.lean >/dev/null
git show archive/winddown-20261014-validation-scratch:semantics/Goose/Construct/ExecutionChecks.lean >/dev/null
git worktree list --porcelain | sed -n 's/^worktree //p' |
while IFS= read -r path; do
    test -z "$(git -C "$path" status --porcelain --untracked-files=all)"
done
```

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
- Hard stops, each of which parks the item and moves on: an action outside this repository other than reading the Aincrad3 checkout and the upstream draft pull requests of O7; anything §7 forbids; a loop that cannot check anything. Under the current working contract, pushing and opening external pull requests require a separate owner request; keep O7 at locally prepared drafts until then.
- Fix on the way, in its own commit, what is egregious: a loop command over 5 minutes on a quiet host; a CPU-time regression over 2× against the baseline on a command whose new flags are absent; a test red on the baseline that blocks the item. Record anything else and leave it.
- Parity before optimization. No item of phase P3 starts while a P1 item is neither done nor parked.
- A failing item gets three attempts, each ending in a root-cause statement (`root-cause`); Tier B theorems get two. Then it is parked with a finding, and work continues with whatever does not depend on it.
- Measure honestly. Time-based numbers are taken only when `perf-gate-ready` exits 0 before and after; otherwise write "perf gate deferred: host busy" and continue. A deferred gate never counts as passed and blocks only the close. Structural gates, which count events, always run. No speedup is stated that was not measured, and every number is vetted with `benchmark-checklist`.
- Bookkeeping is minimal: no provenance, hashes or manifests beyond what a deliverable needs.
- Run as wide as file ownership and memory allow (`orchestrate`). Start with four lanes; widen from measured peak memory, keeping 16 GB free. Budget 4 GB for a C++ lane building at `--parallel 4` (the compiler's own build peaked near 2 GB) and 8 GB for a Lean lane. Aincrad3 measurements are run by the integrator alone, one at a time.
- Lanes are `worker`. The lanes proving `TH-SAFE-01` and `TH-LOWER-01` and the theorem-statement reviewer are `expert`. The final adversarial review is `god`.
- Lane worktrees are `.work/wt/<lane>` on branch `goose-ir-<lane>`; each builds in its own `build/`. The integrator verifies merged commits from `.work/wt/verify`. Keep all scratch under `.work/`. After a lane merges and its checks pass on the merged tree, the integrator removes its worktree and deletes its branch; a parked lane keeps its branch.
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
| O9 | Corpus reach has no percentage target (2026-10-13). The target is completeness within the profile: every repository program whose features all lie in the implemented profiles exports, validates and agrees, with each exception explained. Reach is reported at each profile gate beside a forecast of what the next feature set would unlock (`S3b`), and any floor is set from that forecast, by the owner, after it exists. |
| O8 | The host stays noisy for the rest of the campaign (2026-10-12). The final verification gates of an O7 pull request — the before/after measurements, the exact Docker reproducer against the pushed fix commit, the push itself and opening the draft — are deferred until after the campaign ends. During the campaign a confirmed defect gets its fix branch, its regression test, its locally verified reproduction and its drafted description, and is listed in §14. |
| O7 | A genuine compiler defect found along the way gets a draft pull request to upstream, following the guidelines. They are in two places: this repository's `AGENTS.md` ("Upstream pull requests") and the Aincrad3 checkout's `docs/GOOSE-WORKFLOW.md`; where they differ, the stricter applies. In short: the defect violates a supported language or runtime contract and is confirmed on the failing baseline; it is reduced to a small public fixture; the fix branch starts from upstream `master` and carries one fix, its regression test and no fork tooling; the exact Docker reproducer is run locally with Clang 23 and the current stable GCC and shows the baseline failure and the fixed result; a before/after `test/goose_in_goose` comparison and the affected normal workloads are measured on a quiet host; the title is a Conventional Commit and the body is What, Why, How, Testing, Reproduction; the pull request stays a draft and is never merged by the executor. Linter defects are fork matters and are not sent upstream. The fix is also cherry-picked onto `master`. |

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
| Known failures | None since `2de048a`. Before it — Baseline suite: 8 failing checks, all the same cause. `native_stack_overflow` and `render_reference_cycle` do not print the expected native-stack-overflow diagnostic on this host, at `-O0` and `-O2`, native and JIT. Skips: 31 audio, gfx, physics and ui fixtures and 5 such samples (layers not built), 17 fixtures and one sample the JIT cannot run. Linter suite and the fuzz self-tests (89) pass. |
| Loop timings | **perf gate deferred: host busy.** On the busy host, as orders of magnitude only: one fixture with `--only` about 2 s; the full baseline suite about 37 s; the linter suite about 5 s; a clean `lake build` of the skeleton a few seconds. No loop command is near the 5-minute threshold. |
| Compiler build peak memory | About 2 GB for the largest process of a Debug build. |
| Phase timing in the compiler | None exists. |
| Single-fixture filter in `test/run_tests.py` | `--only GLOB` (fixtures by `category/stem`, extras as `extra/NAME`) and `--goose-arg ARG` (every fixture and sample compile; not the bootstrap, the emitted-C shape checks, or the lexer and shader probes). |
| Aincrad3 | Available. Commit `ef1e1ef33b96fa68748e4ecf3cad37153a4de59c`, extracted to `.work/aincrad3`; its one generated source file is copied from the checkout's own staged build output. Entry point `src/world-core-continue.goose`. `goose --check` (Debug compiler, `-O1`) reports 14,642 specializations, 8,861 inlined calls, and a 1.5 GB compiler peak. Not a timing baseline. |
| Historical figures (issue #9, 2026-10-11) | 14,575 specializations typechecked; 66,026,053 bytes of C; standalone emission median 43.150 s. Emission only: not native compilation, linking or runtime. Not a baseline; `B1` remeasures. |
| Parity reference | `.work/build/base3/goose`: `master` with the same upstream commits merged and the same runtime fix cherry-picked, built from a scratch checkout. `base2` (without the runtime fix) and `base` (pre-merge) are kept only until lanes started against them have reported. |
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
| `S4` | M | T1 | References to slice variables in `core-pilot`: content roots in the context annotation, `V-ROOT` and `V-CALL` for stores through such a reference, the safety proof extended, the exporter's `unsupported` lifted. | The `order` fuzz lane exports without `unsupported`; 2000 seeded cases agree; the audit still lists `TH-SAFE-01`. |
| `T1` | L | S1 | `TH-FUEL-01`, `TH-CORE-01`, `TH-MEM-01`, `TH-MEM-02`, `TH-SAFE-01` for `core-pilot`. | **`G-PILOT`.** |
| `T2` | M | S1 | `TH-ERASE-01`, `TH-SHARE-01`, `TH-SHARE-02`, `TH-REUSE-01`; the quotient checker as an executable (`goose-semantics share`). | Audit lists them; the witnesses and counterexamples of validation plan §4.2. |
| `S5` | L | S2 | GIR-H in C++: data structures, Core lowering, verifier, `--emit-gir-high`. | `test/compiler_gir.cpp` cases `VER-02`–`VER-06`, `VER-09`. |
| `S7` | L | S1 | Lean GIR-H: syntax, `run`, validator, decoder, the Lean lowering. | The C++-exported GIR of every pilot fixture validates and runs to Core's result. |
| `S6` | L | S5 | GIR-L, placement, the C emitter, `--pipeline gir`, `--emit-gir-low`. | Pilot fixtures and lanes agree across legacy, Lean and `gir`, release and debug, native and TinyCC. |
| `T3` | L | S7 | `TH-GIR-01`, `TH-LOWER-01`. | **`G-GIR`** with S6. |
| `S3b` | S | S2 | The exporter reports every unsupported feature of a program, not only the first (`--emit-core` with a report-only mode), and corpus mode prints, for each set of features, how many programs it alone would unlock. | The forecast table in §11; and for the current profile, no program whose features are all supported is left unexported without a stated reason. |
| `S8` | L | G-PILOT, S6 | `core-shrink` through every layer, flat fixed structs first, then shrink operations and their Tier A theorems. The struct encoding contract is specification §§12.4–12.5. | First struct slice: validation `STR-01`–`STR-08`. **`G-SHRINK`** still requires `MEM-04`–`MEM-07`; `resize`, `reference`, `trap` lanes agree. |
| `S9` | XL | S8 | `core-construction` through every layer; `TH-EXIT-01`; `TH-CON-01` as Tier B. | **`G-CONSTRUCT`**: `CON-*`, `EXIT-*`. |

`S8` staging, planned and not a gate result:

1. Specify the profile-selected struct tables, nominal identities, field permissions, and Core/GIR-H tags in [the struct contract](goose-ir-spec.md#124-flat-fixed-structs-in-goose-core02-core-shrink). Pilot artifacts retain their current arity and bytes; the GIR extension is relative to `gir-h/0.3`.
2. The first executable integration delivers the scalar-field local fixture of [validation §6](goose-ir-validation.md#6-semantic-fixture-matrix) through source export, Lean Core, GIR-H and native GIR, including safe unaligned scalar emission. The Core and exporter/lowering changes may land as separate commits before that integration. It includes copying and the independent nominal/permission rejection cases, and keeps whole-object const qualification and temporary field projection explicitly unsupported.
3. Extend to nested flat structs, array fields/elements, field references, globals, parameters/results, defaults and pads; add temporary projection and whole-object const only with their explicit contracts. Equality compares real fields and ignores pads. Repair the applicable memory, fuel, safety, sharing and lowering proof cases and audit the claims actually extended.
4. Add shrink operations with a demand-sensitive invariant; qualify `MEM-04`–`MEM-07` and the bounded resize/reference/trap lanes. A flat-struct result does not establish shrink safety or the parked whole-profile lowering theorem.

The Lean Core struct slice now has strict decoding/writing, nominal record values, field places, layout and permission validation, and executable fixtures for copying, initializer order/abort, nested field permissions and later-global field address formation. Nominal heterogeneous record typing, field-path lookup, record writes/copies, and the constructor/field cases of the fuel, memory, safety and sharing proofs pass the axiom audit; the exported Tier A statements are preserved. The canonical Core writer is `Goose.Core.Writer`. Lean GIR-H struct syntax, evaluation, typing, validation, JSON and Core lowering are now integrated. These Core and GIR results do not close `STR-01`–`STR-08`, `MEM-04`–`MEM-07`, `G-SHRINK`, or the parked whole-profile lowering theorem; full source-to-native coverage remains a separate step.

Build track. It starts at the same time as `S1`.

| ID | Size | Prereq | Work | Acceptance |
|---|---|---|---|---|
| `B1` | L | G0, G2 | Stable keys (`DeclKey`, `TypeKey`, `ContextKey`), SHA-256, phase timers, per-function byte accounting, dimension attribution, `--build-report FILE`. All inert without the flag. Then the integrator runs it on the synthetic family and Aincrad3, writes the counts and phase split into §3, and freezes the budgets. | **`G-ATTR`**: the report passes validation plan §9.2; §3 names the dimensions behind the growth and the split of the loop among costs (a)–(d). |
| `B5` | M | G2 | The synthetic family in full: shareable and must-stay-distinct members, the edit transformations with expected changed sets, `test/scale/edit_matrix.py`, the Aincrad3 runner. | The family's expected checked-context counts match the base compiler; the matrix runner reports `E00` on the single-file path. |
| `B2` | L | B1 | A naming seam in the legacy backend with the existing scheme as default and a stable-key scheme; lowering-key and consumed-assumption recording; canonical-body classes over call-graph components; `--share`. | **`G-SHARE`**: `L-SHARE`; the baseline suite passes with `--goose-arg --share`, which the runner does not apply to its four checks that read the shape of emitted C; default output byte-identical to the base. |
| `B3` | L | B2 | Unit assignment and unit text per specification §17: per-unit declarations, module globals segments, literals by content, location tables, stable nonlocal target ids, the program unit; `--emit-units DIR`. | Every runnable fixture and sample builds from its units and matches its expected output; unit text is identical across two runs and across `-j`. |
| `B4` | L | B3 | `goose build --units`: the store, completion records, locking, parallel batched native compilation, link skip, the recording reader and R0, `--rebuild`, `--verify-reuse`. | **`G-UNITS`**: `L-NOOP`, `L-LEAF`, `L-LOC`, `L-ADD`, `L-EQ` on the synthetic family; first Aincrad3 edit-loop table in §11. |
| `B6` | L | B1 | Dependency sets recorded in the checker under the report flag; invalidation prediction in the report. No reuse acts on it. | Validation plan §10.3's shadow rows: no under-approximation on any matrix edit. |
| `B8` | L | B4 | Units for programs that include C of their own: one native-support unit holding the `--include` headers and sidecar C with whatever of the runtime they need to see, external entry points for the extern functions other units call, and header-visible generated type names (every type reachable from an extern or export signature, derived slice and array types included) spelled as in single-file output. | The corpus programs that link C of their own build and pass in units mode instead of being skipped; Aincrad3's core entry builds and runs in units mode with at most a recorded two-line change to its scratch copy; locality still holds for a body edit in such a program. |
| `B7` | S | S6, B3 | The GIR-L emitter produces instance text through the unit interface. | Pilot fixtures pass under `--pipeline gir` in units mode. |

### 4.4 P2 — hardening

| ID | Size | Work | Acceptance |
|---|---|---|---|
| `H1` | M | The rest of validation plan §7. | Implementable cases fail under their named diagnostics. VER-04 shrink and VER-05/06/10 caller-destination cases await S8/S9; VER-07 awaits O1. |
| `H2` | M | `E10`–`E16`, and the seeded randomized edit sequence under `--verify-reuse`. | **`L-FAIL`**; no divergence from a clean build. |
| `H3` | M | Validation plan §8, including a `--units`-built `goose-lint` run through the linter suite. | `LINT-01`–`LINT-08`. |
| `U1` | rolling | For each suspected compiler defect a lane or the integrator reports: confirm it against the language specification on the upstream compiler, and if it is genuine, carry out O7. A suspicion that does not survive confirmation is recorded in §12 with the reason. | The draft pull request's own reproducer and checks, quoted in §11; or the §12 line. |
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
| 10 | `H3`; `python3 test/scale/parity.py --goose <candidate> --baseline .work/build/base3/goose`. |
| 11 | §11 filled from the validation plan's template. |

## 7. Contract changes

**Pre-authorized, all additive and opt-in:** the flags `--emit-core FILE`, `--emit-gir-high FILE`, `--emit-gir-low FILE`, `--pipeline legacy|gir`, `--build-report FILE`, `--share`, `--emit-units DIR`, and for `goose build`: `--units`, `--rebuild`, `--verify-reuse`; the report format `goose-build-report/1`; the store directories under a program's existing build directory; `src/runtime/runtime_units.h`; `--only` and `--goose-arg` in `test/run_tests.py`; `--semantics` and `--pipeline` in `fuzz/driver.py`; new files in `CMakeLists.txt`'s source list; new entries in the C++ unit-test list.

**O7 local preparation:** build and verify one fix branch per confirmed defect and prepare its draft description. Pushing the branch or opening an external pull request requires a separate owner request under the current working contract.

**Forbidden:** changing the behavior or default output bytes of any existing command; facts v1, diagnostics v1, contracts v1, lint configuration, baselines, lint statuses, warning text; `docs/goose_spec.md`; existing fixtures and expected outputs; the five existing runtime files; the checker's acceptance of any program; `.github/workflows`; a new dependency in C++ or Lean; making any new mode the default. The owner redirected campaign work to `master` on 2026-10-14, superseding the original branch restriction.

Each change made is appended to §8.

## 8. Contract changes made

*(append-only; one line per change: what, where, why)*

- `test/run_tests.py`: `--only GLOB` and `--goose-arg ARG`; `samples/run_samples.py`: `--goose-arg`. Loop repair and whole-suite runs under a new mode.
- `goose --build-report FILE`: writes `goose-build-report/1`. Rejected with `--tokens`, `--dump`, `--parse`, `fetch` and `--multi-test`.
- `goose --emit-core FILE`: writes a `goose-core/0.2` module for `core-pilot`, or fails with `error: unsupported in core-pilot: <feature-id>`.
- `goose --emit-core-report --check FILE`: writes one sorted, unique JSON set of every unsupported Core-profile feature and no Core or C artifact. It is rejected with parsing, output, build and runtime modes.
- `goose --share`: merges emitted functions with equal bodies. Default output unchanged without it.
- `goose --stable-names` (hidden, not in the usage text): names emitted functions, types, literals and nonlocal-target ids from stable keys. A seam for unit output; not pre-authorized by name, added because unit output needs it testable on its own.
- `goose build --units` with `--rebuild` and `--verify-reuse`: builds through units with a persistent object store under the program's build directory; without `--units`, `goose build` is unchanged. `--pipeline gir --emit-units DIR` writes IR-built units.
- `goose --emit-units DIR`: writes the program as C translation units, one runtime header and a link list; implies stable names; composes with `--share`.
- `goose --emit-gir-high FILE`: writes a `gir-h/0.4` module; the verifier runs on every lowered module.
- `goose --pipeline legacy|gir` (default `legacy`): with `gir`, `-o`, `--standalone` and `--jit` produce C from the IR pipeline; features outside the profile fail with `error: unsupported in pipeline gir: <feature-id>`. `goose --emit-gir-low FILE`: writes a `gir-l/0.2` module (specification §12.3; no reader exists for it).
- `goose-semantics` (new tool, test-time only): `audit`, `run`, `validate`, `share`, `lower`, `gir-validate`, `gir-run`, `gir-reencode`, `agree`.
- `fuzz/driver.py`: `--semantics TOOL`, `--pipeline NAME`.
- `Construct.Roots`: source-owned `RootAlias`, `RootSetsOverlap`, `AliasClosure` and accepted module/body root facts replace provisional proof-only alias vocabulary; runtime checking and errors remain equivalent.
- `Lower`: canonical child metadata, exact retained rows and generated instruction occurrences strengthen source-demand proof interfaces; scoped static coverage does not establish the full runtime demand theorem.
- Construction proof frames now require physical object and ordinal registration plus uninitialized-key absence; actual entry, binding, static-byte and allocation transitions preserve these freshness contracts.

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
 legacy optimizer --> --specs/BCE      Typed Goose Core --> Lean: validate, eval, proofs
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

### 11.1 `G-ATTR`: cost attribution, first run

Candidate `8364929` against base `62366eb`. Alpine Linux, musl, x86_64, Clang 23.1.3. Compiler built Debug. **Perf gate deferred: host busy**, so every time below is a share of one busy run of a Debug compiler, good for ordering phases and nothing else. Counts and bytes are exact. Budgets are not frozen.

Checks: the report passes its consistency check on the synthetic family, the linter's source, three large fixtures and samples, and Aincrad3 (456 of 66,636,122 bytes unattributed). Default emitted C is byte-identical to the base compiler's on 1,230 emissions. Stable declaration keys survive an added function, reordering, a comment and a body edit.

Aincrad3 core entry, `-O2 --standalone`:

| Count | Value |
|---|---|
| Source functions | 6,481 |
| Checked contexts | 14,642 |
| Entry-reachable contexts (the linter's fanout population) | 7,454 |
| Live instances after optimization, all emitted | 4,701 |
| Source functions with a live instance; with more than one | 3,687; 529 |
| Call sites inlined; nodes copied by inlining | 24,307; 552,184 of 1,396,395 live nodes |
| Emitted C | 66,636,122 bytes: function bodies 65.2 MB, prototypes 0.56 MB, literals 0.53 MB, types 0.21 MB, runtime text 0.13 MB |

What this says about the four costs:

- **(b) Emitted code is mostly not duplicated specializations.** Only 1,014 of the 4,701 emitted bodies are second or later instances of a source function. If every one of them shared a body with its first instance, at most 19.2 MB (29%) of function-body bytes would go; the real figure is lower, because some differ by type. About 40% of live nodes are inlined copies. The 500 largest functions hold 66% of the bytes.
- **(a) Checking is multiplied more than emission is.** 8,206 contexts are second or later contexts of their function, and 7,188 contexts are not reachable from the entry at all. The depth key is the dimension behind most of it: about 3,700 contexts exist only because of it, then held-exactness (about 1,100) and bound function values (about 800). Concrete types and pools are behind almost none.
- **Compiler phases**, shares of CPU in this run: check and specialize 44%, code generation 19%, bounds-check elimination 18%, report collection 15%, optimize 3%, parse 1%. Compiler peak memory 1.6 GB.
- **(c) and (d) are not measured yet**: no native compile or link of the emitted C has been run.

Consequences for the sequence: native-unit reuse (`B3`, `B4`) is the item that can change the edit loop most, since it applies to all 66 MB. Sharing (`B2`) is bounded at 29% of bytes on this workload. Inlining at `-O2` is a larger source of emitted code than specialization and is not addressed by sharing; a development build at a lower Goose `-O` level is the available lever and is measured in `B4`. Check time is the largest compiler phase and is multiplied about 2.3× by contexts, which is deferral `X1`'s subject.

### 11.2 Sharing, first measurement

Candidate `f37196b` rebased onto the upstream merge. Same environment and the same caveat: sizes and counts are exact, nothing here is a timing.

Checks: the baseline suite passes with `--share`, with `--stable-names` and with both, apart from the two known reds; the synthetic families give exactly their expected implementation counts at `-O0` and `-O2` with every must-stay-distinct pair still distinct; emitted names under `--stable-names` survive an unrelated function, new specializations, a reorder, comments and a body edit; default output equals master-plus-upstream on 1,232 emissions.

Aincrad3 core entry:

| Goose level | Live bodies | Calls inlined | Emitted C | With `--share`: bodies | With `--share`: emitted C |
|---|---|---|---|---|---|
| `-O0` | 7,430 | 0 | 52.3 MB | not run | not run |
| `-O1` | 5,213 | 8,861 | 56.3 MB | 4,438 | 47.4 MB (−15.8%) |
| `-O2` | 4,701 | 24,307 | 66.6 MB | 4,079 | 56.5 MB (−15.2%) |

- Sharing removes about 15% of emitted C on this workload, half of the 29% bound. Of the same-declaration bodies that did not merge at `-O2`, 181 differ in inlined calls, 98 in a callee, 23 otherwise, and none only in bounds-check sites. Sharing before optimization (`O2` in the sequence) would address the 181; its gate asks for 10% of emitted bytes, which the report does not yet express in bytes.
- §11.1 overstated inlining. With no inlining at all the program is still 52 MB; inlining at `-O2` adds about 14 MB while removing 2,700 bodies. The bulk is the program itself.
- No effect on check time, as designed: every context is still checked.

### 11.3 Units and reuse, first real-program run

Candidate `f0aa066`. Debug compiler, busy host: counts are exact, times are one noisy run each and only show orders of magnitude. **Perf gate deferred: host busy.**

The merged-tree run recorded the following results before the H2 harness audit: the units edit matrix passed every row with reuse verification on (cold 7 units; warm no-op runs nothing; comment edit recompiles one locations unit and no code unit; leaf edit one unit; contract changes rebuild everything and return warm; damaged, truncated and half-published entries are detected and rebuilt; a failing edit reports its error and no stale success), a seeded 60-step random sequence did not diverge from a clean build, 575 corpus programs built from units with none failing, locality and dependency checks passed, and the full suite was green. These are historical results; they do not establish the audited H2 assertions.

**H2 structural acceptance passed at `c1070ef0`.** The Debug compiler passed E10–E16 and the 60-step randomized sequence with seed 1 under `--verify-reuse`. E13 passed both observed interruption points and clean-build recovery. E10 covered its CLI profile, define, compiler and binary variants, then probed `UnitContractValues.c_flags`, `.target` and `.runtime_version` through `MakeContract` and `BuildUnitObjects`. The target probe used the host compiler with a synthetic target identity. The runtime probe changed the runtime identity without rebuilding the runtime text. E10 therefore qualifies the production builder boundary for these contract fields, as recorded in the standing decisions. It does not establish CLI selectors for those fields, cross-compilation, or a runtime-text-only full compiler build. These runs establish correctness, not performance.

Before `B8`, Aincrad3's core entry did not build in units mode for two reasons in its included native headers: they read runtime-internal state that exists only when the runtime is pasted into the same translation unit, and they spell compiler-generated C type names. The public corpus had the same unqualified boundary for programs that link C of their own.

After `B8`, the core entry builds as 459 units at Goose `-O0`. A run with the real package and schemas exits successfully after one bounded step and writes its checkpoint. The first native build produced all 459 objects but its link target directory disappeared before the linker ran; repeating with the executable directly under the scratch checkout reused all 459 objects, linked, and ran. This makes the successful row a recovery build rather than a clean cold-build measurement:

| Build | Frontend | Units | Native objects | Link | Result |
|---|---|---:|---|---|---|
| Recovery after failed link | ran | 459 | 459 reused, 0 missed | ran | executable ran one step and wrote a checkpoint |
| Warm, nothing changed | did not run | 0 changed | 0 compiler processes | skipped | warnings replayed; executable retained |

The report records 14,642 checked contexts, 7,430 emitted bodies and a 1.55 GiB compiler peak. The host was busy before the run, so its elapsed and phase times are discarded: **perf gate deferred: host busy**. Edit-locality rows follow from the `B5` Aincrad3 matrix rather than this recovery run.

The `B5` matrix then ran the core entry at `-O0` with one immutable Debug compiler binary. Every reused object was checked against a fresh native compilation:

| Row | Source change | Unit text changed | Native result | Link |
|---|---|---:|---|---|
| `E00` | cold build | 459 | 459 misses in 187 compiler invocations | ran |
| `E01` | none | 0 | no compiler process; frontend did not run | skipped |
| `E02` | comment and blank line above `argument_u64` | 1 location unit | 458 reused, 1 missed | ran |
| `E03` | commute one addition in `argument_u64` | 1 code unit | 458 reused, 1 missed | ran |

An earlier matrix attempt was discarded because its compiler executable was relinked between `E02` and `E03`. The unit contract intentionally includes the compiler binary digest, so that run correctly selected a new store. The fixed-binary run above is the locality evidence. Its times overlapped host load and are not measurements: **perf gate deferred: host busy**.

A smaller Aincrad3 entry point that needs no native headers (2,228 specializations) does build, as 38 units, at Goose `-O0`:

| Build | Frontend | Units with changed text | Native compiler | Objects reused | Link | Wall, one busy run |
|---|---|---|---|---|---|---|
| Cold | ran | 38 | all | 0 | ran | about 23 s |
| Warm, nothing changed | did not run | 0 | 0 processes | — | skipped | 0.05 s |
| Comment appended to the entry file | ran | 0 | 0 processes | 38 | skipped | about 11 s |
| Body of one function edited | ran | 2 (its code unit and locations unit) | 1 process, 0.13 s | 36 | ran, 0.07 s | about 12 s |

- Native-unit reuse does what it was built for: after a body edit, native work falls from roughly half the cold build to a fifth of a second.
- What remains is the frontend, exactly as §5 warned: about 11 s of a 12 s edit. Of that, in CPU time, code generation 2.6 s, checking 1.1 s, bounds-check elimination 1.0 s — and **report collection 4.5 s**, so the report with dependency recording roughly doubles the frontend's cost on this program and must not be on in a timed loop. That overhead is far over the proposed 10% and goes back to the lanes that own it.
- A Release compiler will shrink all frontend numbers; a Release build exists for the next run. None of this is a baseline.

Open from the first run, both resolved in `4fcc480`: the 266 indistinguishable contexts were a missing key dimension (a bound function value's environment was named by its base only), and report collection lost its repeated work. The paragraph below is kept as first written.

Open from this run: 266 contexts are indistinguishable under every recorded key dimension, so the context key is not yet injective; and report collection costs more than the proposed 10%. Both go back to the `backend` lane.

### 11.4 Unsupported-feature forecast

Candidate `7efc196`. `--emit-core-report` was checked against normal Core export over all 582 positive fixtures and samples. It found 77 agreements, 504 unsupported programs, no mismatch or harness failure, and the known unbounded-recursion case that exhausts Lean fuel. The 504 unsupported programs form 429 exact feature sets; corpus mode emits all of them in its JSON result.

Single-feature sets give the programs one feature alone would unlock:

| Feature | Programs | Feature | Programs |
|---|---:|---|---:|
| `string-value` | 6 | `reusable` | 4 |
| `struct` | 4 | `elementwise-arithmetic` | 3 |
| `float` | 3 | `extern-fn` | 2 |
| `multiple-results` | 2 | `return-from` | 2 |
| `captured-reference` | 1 | `fill-grow` | 1 |
| `shrink-operation` | 1 | `thread` | 1 |
| `variable-array` | 1 |  |  |

The most common exact multi-feature sets are `string-value + struct` (7 programs), `float + string-value` (5), `shrink-operation + stored-reference + string-value + struct` (4), `print-argument + string-value` (4), `optional + rebind-target + struct` (4), `call-arity + function-value + thread` (4), and the two `adt + function-value + match + struct` sets, without and with `string-value` (4 each). The forecast replaces the earlier first-failure histogram: flat structs alone unlock four programs, while 353 other struct-using programs also need at least one more feature.

## 12. Decision log

*(append-only; one line per judgment call: the call and why)*

- Aincrad3's core entry imports a source file that its build generates and does not track. Copied it from the checkout's existing staged build output instead of running its generator, which reads another private repository: reading the checkout is within O5, the generator's input is not.
- Suspected defects so far, for `U1`: (1) `native_stack_overflow` and `render_reference_cycle` do not print the native-stack-overflow diagnostic on this musl host — under investigation; (2) `redundant_cast` lint warnings carry no specialization contexts, against the facts documentation — confirmed: the warning is pushed with an empty list (`src/typecheck_exprs.h:2449`), visible only in non-generic code because casts in generic bodies are never judged; it predates the branch and is a linter matter, so it is left for the owner as a fork issue, not sent upstream and not changed here; (3) `print` writes its line after evaluating all arguments, where the language text can be read as rendering in order — recorded as a model decision, not a defect, because the text does not say when bytes reach the output. The Lean model and the compiler have disagreed on no program yet.
- The safety proof justified itself as a check and not only as a certificate: random mutation of example modules (62,000 mutants) had found no accepted-then-faulting module, and the proof found three. The Lean validator is stricter than before in those cases, and the IR-side effect computation does not yet apply the second fix (a call charging the caller with the globals a callee context lists for a parameter); aligning the IR validator, the C++ verifier and the exporter's summaries with it is a follow-up for the `sem-gir` and `export` lanes.
- An attempt at a failing item is one lane session that ends with the acceptance check red and a root-cause account. The first session on `T1` proved fuel monotonicity, the growth theorem and the per-operation invariant lemmas, and stopped short of `TH-SAFE-01` on proof volume and architecture, with no counterexample found. The second attempt goes to a `god` lane, which the routing rules reserve for work an `expert` has failed on with evidence, and it may restructure the validator but not the evaluator.
- Aincrad3's core entry is measured through a smaller entry point of the same project until `B8`. Adapting its native headers in the scratch copy to make the core build today would have measured a program that does not exist; the honest statement is that units mode does not yet serve programs whose included C depends on single-file output.
- Sharing classes are computed by partition refinement to a stable partition, not by ordering call-graph components as first specified. It merges a superset of what the component method would, is independent of creation order, needs no rule for unorderable components, and is exactly the congruence the sharing theorem assumes. Specification §16.2 now says so.
- Nonlocal-target ids under stable naming come from the target's context key, not its declaration key: the legacy protocol distinguishes target specializations, and two contexts of one target need distinct ids.
- A reference to a slice variable (a `T[:]&` parameter, or a captured slice variable after closure conversion) is outside `core-pilot` for now: the exporter reports it unsupported. Writing a slice through such a reference is a stored reference, which needs content roots in the annotation and in the safety invariant; adding that while the safety proof is in progress would move its target. It returns as item `S4` after `T1`, because the `order` fuzz lane relies on it.
- `return`, `break` and `continue` inside an expression block are outside `core-pilot`: the Lean validator rejects them and the exporter reports them unsupported. Modelling them needs a body result threaded through expression evaluation, which the pilot's proofs do not need.
- Historical lowering comparison: the original plan required C++ and Lean to reproduce the same GIR bytes. The 2026-10-25 recovery supersedes that policy for independently optimized lowering. Each emitted module must validate and agree with Core on the checked fixture outcomes. Canonical reencoding and deterministic exports remain byte comparisons. These finite checks do not prove the C++ lowerer correct.
- `V-ROOT` no longer requires a same-scope root to be declared first. The compiler accepts rebinding a reference to a later-declared variable of its own scope, and that is safe because a scope's variables end together; the stricter rule would have rejected valid programs for no safety gain.
- Unary minus on an unsigned type is a compile error in Goose. The numeric model keeps a total definition for it; the Lean validator rejects it under `V-TYPE`.
- The checker already groups roots into classes: one helper called with many distinct globals and many locals at different depths gets two specializations, not one per call site. The synthetic family therefore has to vary the dimensions that do multiply specializations; `B1`'s dimension attribution on Aincrad3 says which those are, and `B5` builds its members from that.

## 13. Campaign log

- **Paused 2026-10-26 after requested winddown and cleanup.** Integrated every ready coherent lane checkpoint through `0df2c602`; final 201-module lowering and 245-module construction checks passed on pinned Lean 4.35.0 with allowed axioms only. Parked the underconstrained owning receipts and conditional family on committed branches, stopped all lanes, retired 23 checkouts, and reduced `.work/` from 80.6 GB to 11.6 GB while preserving verified compressed evidence. Clean-environment resume inspection and the closeout guard passed. Full accepted-execution proofs and performance qualification remain open; no push by this workflow.

- **Resumed 2026-10-17 at the owner's request.** Integration starts from `8eb50c00`, which includes upstream updates after the pause. Campaign closeout is inactive. Five lanes resume accepted-state lowering, construction GIR, native handlers, whole-execution proofs, and independent Core audit registration. Retained per-lane Lean caches are empty. Seed focused builds from a copy of the main checkout's `.lake/build`, then let Lake revalidate inputs. The external Aincrad3-owned worktree is preserved. No new gate result or performance claim is made.

*(append-only; one line per gate or phase end. Resumed entries here supersede
the pending statuses in the paused handoff above.)*

- **`O1` is parked after the third proof attempt; `G-BCE` was not reached.** GIR-H revision 0.4 carries per-function fact certificates and `i_index_proven`; the C++ proposer and verifier, Lean decoder/writer/checker/interpreter, lowering, and adversarial `GIR-V080` fixtures are implemented. The rule set is deliberately limited to nonnegative constants, signed i64 less-than true edges, array lengths, and snapshots; every storage mutation, call, and scope transition kills mutable-length facts. The local Lean results prove the executable checker's structural derivation, all four fact rules, syntactic index justification, equality of one proven index with its checked form, and preservation through an arbitrary continuation after that instruction. They do not prove that the certificate facts hold in every reachable runtime frame. Attempt 1 extracted the declarative certificate derivation but exposed that missing semantic invariant. Attempt 2 proved each narrowed rule sound in the runtime fact interpretation but did not propagate the interpretation through all other instructions and edges. Attempt 3 proved the single-instruction replacement with an arbitrary continuation, but whole-function induction still requires frame preservation across calls, CFG joins and loops. Therefore `TH-BCE-01` and the semantic conclusion required by `TH-CERT-01` remain deferred. `VER-07` passes, while the theorem gate and the pilot-corpus proven-index acceptance requirement do not: ordinary lowered pilot functions currently expose their loop values through slots, so they propose no proven index. The opt-in GIR implementation remains executable and checked, but carries no `G-BCE` claim.
- **`O2` is parked because its admission gate did not hold.** On Aincrad3 commit `ef1e1ef33b96fa68748e4ecf3cad37153a4de59c`, compiler tree `1a9a56f4` at Goose O2 with `--share --standalone` emitted 56,546,439 bytes. The current report attributes 5,555,043 bytes to the two context-dependent causes admitted by the gate: 5,555,043 from inlined calls and 0 from bounds-check sites, or 9.82% of the emitted C against the required 10%. `report_check.py` passed the report and C-file consistency checks for 6,481 functions, then rejected only `--require-o2-sharing-threshold`. Counts remain 4,701 bodies before sharing and 4,079 after; callee and other differences are outside the O2 admission numerator. This was a deterministic byte/count qualification, not a timing measurement.
- **`S8` is parked after the third `TH-LOWER-03` attempt; `G-SHRINK` was not reached.** Through `1a9a56f4`, the implemented `core-shrink` slice has demand-aware Core safety, flat-struct and shrink execution through Core/GIR/native, exact abort-order fixtures, conservative returned-owner provenance in GIR-L, and clean bounded differential gates. The final merged-tree checks passed: 7 selected `MEM-08`–`MEM-11` semantic GIR agreements with no mismatch or unsupported case; 22 focused source checks, 11 generated-C cases at O0/O2, one debug run, and 12 JIT runs; the shrink boundary and pre-publication rejection scripts; the `MEM-12`–`MEM-14`/struct contract including Clang 23 alignment sanitization; and the 106-declaration Lean audit with only `propext`, `Classical.choice` and `Quot.sound`. The three 2,000-case resize/reference/trap gates and their sanitizer smokes remain the bounded random evidence recorded below. The phase cannot satisfy the validation contract because the required Tier A theorem is still missing: the current Core-to-GIR relation has no mapping from demand points and retained operands to GIR program points and SSA values, and its postcondition leaves frame cells unlabelled. `Goose.Proofs.GIRFuel.run_nonTimeout_fuel_mono` is the useful result from attempt 3, but it preserves faults as well as successes. Broader captured/global/recursive/same-owner `MEM-05` combinations and self-recursive returned-owner inference remain conservative unsupported boundaries rather than gate results.
- **`S9` is parked on `S8`.** `core-construction`, `TH-EXIT-01`, `TH-CON-01`, and `G-CONSTRUCT` were not started because the campaign orders them after S8 and the prerequisite ended parked without `G-SHRINK`.
- **`S8` Core proof closure and bounded shrink qualification completed through `878144e4`; `G-SHRINK` is still open.** The demand-indexed frame proof now covers every evaluator component, including calls, all loop forms, `pop`, `pop_n`, `clear`, `resize` and whole replacement. `Goose.Proofs.Safety` and `Goose.Audit` rebuilt on the merged tree, and `goose-semantics audit` lists 105 declarations using only `propext`, `Classical.choice` and `Quot.sound`. The source/Core/GIR/native flat-struct contract passed with Clang 23.1.3 on x86_64 musl. Full-matrix seeded runs completed with no failure, unsupported case or inconclusive result: `resize` seed 812000, 2,000 agreements; `trap` seed 832000, 2,000 agreements; `reference` seed 822000, 1,400 executable agreements plus 600 expected compiler rejections. Sanitized O0/O2 smoke runs added 8 `resize`, 8 `trap` and 7 executable `reference` agreements, with one expected reference rejection. The exact MEM-06/MEM-07 source fixtures also agree through Lean and the GIR pipeline. Two harness defects found by the gate are fixed separately: shrink abort kinds are classified, and resize append operands stay within the shrink profile; the capacity fixture now names its abort origin. These runs are correctness evidence, not timing measurements. The gate remains open because the required Tier A `TH-LOWER-03` theorem does not exist, the claim ledger still describes the earlier pilot invariant, and the source-to-native qualification matrix remains incomplete for parts of `MEM-04`–`MEM-14` and `STR-02`–`STR-04`/`STR-08`.
- **`S8` integrated proof tranche through `4bde3479`; full closure remains pending.** Shrink authority is tied to observed owners; ghost reference roots are classified for the shrink guard, and retained aliases distinguish limited physical runs. Source-view roots now separate fixed, limited and owner cases, and accepted limited mutations preserve physical storage. Focused checks cover accepted `foreach` behavior and call classification. Access-aware holder typing and replay-root normalization are integrated, with two axioms in the allowlist. The focused `Context`/`Spec`/`Scope`/`ShrinkBridge` tranche passed 28 jobs; follow-up call-preservation, retained-syntax, mutation and `foreach` checks passed 31 jobs. The exact-excerpt `while`/`range` kernels remain green. A production `StepCall3` source slice builds, but is not integrated into the root theorem; the root typing-bridge build is still finishing. The per-element loop kernel, full `Specs`, semantic executable and `G-SHRINK` remain pending exact closure for all step forms. The additional capability-bundle and retention bridge contracts are pending verification on main.
- **Bounded GIR differential:** the doctor case passed and the smoke lane agreed on all 8 cases. Six lanes ran 20 cases each across the full four-combination matrix, with no findings or crashes:

  | Lane | Seed | Agree | Unsupported |
  |---|---:|---:|---:|
  | Aggregate | 680100 | 0 | 20 (`elementwise-arithmetic`) |
  | Numeric | 680200 | 20 | 0 |
  | Order | 680300 | 20 | 0 |
  | Resize | 680400 | 2 | 18 (`temporary-slice`) |
  | Scalar | 680500 | 20 | 0 |
  | Trap | 680600 | 20 | 0 |

  Overall, 82 of 120 cases agreed and 38 were unsupported: 20 aggregate arithmetic cases and 18 temporary-slice resize cases. This compared legacy behavior with GIR native/JIT paths; it used no Lean oracle or sanitizers. The run used the frozen C++ compiler and Clang 23.1.3. No timing or memory result is claimed; performance remains deferred on the busy host, and O8 upstream drafts remain parked.
- **`S8` proof work resumed 2026-10-13; still in progress.** The lexical pilot now frames all future bindings and preserves initialized value-storage types (`PilotStoreLe`). Shrink protection follows the exact checked mutation requests; sampled loop-body demand is tracked. Frames carry initialized non-reference storage roots and visible-binding metadata; call preservation classifies owner capabilities, and scope footprints and retained aliases are carried through release. Typed-call child demand is access-aware: a slice holder stays live through the relevant argument prefix, while an unrelated reference holder is dropped. Exact-excerpt `while` and `range` kernels are green under the three-axiom allowlist, but the per-element loop kernel is incomplete. A limited `foreach` regression has only scratch proof evidence, not full semantic closure. The capability-guard/proof-bridge follow-up is pending. No `G-SHRINK` or `S9` completion is claimed. Executable, audit and fuzz gates await exact closure for every step form; the performance gate is also blocked pending closure and remains deferred because the host is busy. O8 upstream drafts remain deferred.
- `H2` structural acceptance passed at `c1070ef0`, as detailed in §11.3. The E10 builder probes qualify raw C flags, target identity and runtime identity through the production builder boundary. They do not claim CLI selectors, cross-compilation or a runtime-text-only full compiler build.
- `S4` GIR alignment merged as `c4d9d8b` (`gir-h/0.3`): reference content roots and call effects now align across Core lowering, Lean GIR and the C++ verifier, including the Core validator's no-return flow. The commit's focused fixture checks are `gir_never_returns_exit.gir-h.json`, `gir_rejected_v050_root_underapprox.json`, `gir_rejected_v050_slice_content_read.json`, `gir_rejected_v050_slice_param_rebind.json`, and `gir_rejected_v050_call_parameter_global.json`, exercised by the GIR golden and invalid check scripts. No timed gate is claimed here.
- `S4` completed: the order fuzz lane exported without `unsupported` and all 2,000 seeded cases agreed. The Lean Core slice-reference roots and safety proof, Core exporter, GIR lowering/validation alignment, and forwarded-content-root fix are integrated (`ab44a0b`, `aeb9649`, `c4d9d8b`, `5790fd1`, `760158e`). `TH-SAFE-01` remains audited; the exact order-gate result closes S4's stated acceptance.
- Flat structs have integrated Lean Core and Lean GIR slices. Core evaluation, strict decoding/writing, nominal typing, field places, layout/permission validation, fixtures, and the constructor/field fuel, memory, safety, and sharing proof cases are recorded in `26c2154`, `f39b1a8`, `2d28da4`, and `551a733`; Lean GIR syntax, evaluation, typing, validation, JSON, and Core lowering are integrated in `0c4e7cb`, with forwarded slice-root checks in `760158e`. This is the implemented flat-struct slice only: S8 shrink operations and `G-SHRINK` remain active, while S9 construction has contract work but no implementation or gate result in this checkpoint.
- `H4` documentation refresh completed through `21d5f41`: `00e0dd3`, `e04f2a0`, `2a5ef7a`, `0825196`, `da8377d`, and `21d5f41` route repo guidance and refresh the reference, user, compiler/testing, and source-comment documentation. Runtime comments needed special handling because runtime source text is embedded verbatim and hashed into `RuntimeVersion`; the final runtime-comment commit records that constraint.
- `S8` contract update `ca74cc7` was documentation-only and reached no gate. Later commits integrated the Lean Core and Lean GIR flat-struct slices above; shrink operations, remaining validation rows, source-to-native coverage, and `G-SHRINK` are still active. `S9` has contract work only in this checkpoint, with no implementation or gate result.
- **Resumed 2026-10-13.** Starting tree `47fa15a` is clean. Recreated isolated worktrees for IR alignment (`goose-ir-ir-align`), units validation (`goose-ir-units-finish`), corpus forecast (`goose-ir-export-forecast`), and the third and final lowering attempt (`goose-ir-sem-gir`). Upstream drafts remain deferred under O8; nothing is pushed.
- `H4` completed: implementation and testing docs cover the Core/GIR exports, pipeline choice, units corpus package coverage and build flags; the CLI synopsis lists the public Core/GIR, report, sharing and units flags while keeping `--stable-names` hidden. The compiler usage output and `git diff --check` pass.
- `B8` remainder merged: all five `test/packages` fixtures pass through `goose build --units` in 15 O0, O2 and O2-with-sharing builds; Aincrad3's core entry builds as 459 units and runs against its real package and schemas. `B5` now has an Aincrad3 E00–E03 runner; its real edit matrix remains to run. Timing remains deferred because the host is busy.
- `H3` completed: a `goose-lint` companion built with `goose build --units` has zero differences across 393 parity comparisons, and the existing linter suite passes against that sibling install. `LINT-01`–`LINT-08` now hold on the merged tree.
- `T3`, third and final attempt: `stmt_while_sim` proves the actual lowering of a nonnested while statement, and six checked subclaims cover arbitrary enclosing loop contexts, scoped block initializers and conditional loop composition. The audit now lists 88 theorems with the same three allowed axioms. Whole-profile `TH-LOWER-01` is parked: range-loop reentry changes its counter below the current protected frontier, and nested loops, calls and returns remain unproved. The checked prefix lemma records the invariant a follow-on proof would need.
- Independent `T3` review found no proof or claim defect: all seven loop claims are sound within their recorded fragment or explicit composition premises. Focused source and executable audits list 88 entries with the same three allowed axioms; mutation and concrete-instantiation probes passed. Whole-profile lowering remains parked.
- `H1` completed for every implemented decoder and verifier operation. The remaining shrink-summary, construction/escape, caller-destination and certificate rows stay attached to `S8`, `S9` and `O1`, whose operations and checker do not exist yet.
- `S3b` completed after the full corpus gate found and fixed two report-only boundary bugs: bodyless extern contexts were built after being reported, and unsupported standard-library globals bypassed their established skip boundary. The fixed run has 77 agreements, 504 explained unsupported programs, no mismatch or harness failure, and one known fuel exhaustion; §11.4 records the forecast.
- `B5` completed on the real Aincrad3 core entry: `E00`–`E03` all pass, with a true no-op and one-unit locality for both the comment and body edits. The first attempt was discarded because the compiler binary changed during the matrix; the fixed run used an immutable copy. Timing remains deferred because the host is busy.

- `U1`, second and third suspicions: (a) order dependence of checking is **not a defect** — about 43,000 permutations of declarations, imports and files over 1,900 repository fixtures and 9,000 generated programs with reference-holding globals never changed acceptance or behaviour, only which of several correct diagnostics prints first; the language says top-level declarations are order-independent and only global initializers are ordered. (b) **A second genuine defect**: a path package's native C is not rebuilt when its source changes. The rebuild stamp's time is a maximum starting at 0 over file-clock counts that are negative on this C++ standard library, so it is always 0; editing the C source leaves a stale binary, against the package design's "rebuilds when any of its sources is newer than its build". Fix and regression test in preparation on an upstream branch; the pull request is deferred like the first.
- **Paused 2026-10-13.** Wind-down: the lowering lane landed structured control (`lower_correct_ctl`) and kept its loop work as a wip branch; the exporter lane landed result mutability and slice references (`order` fuzz lane 300 of 300 agree; corpus 76 of 77 agree); the rebuild-stamp fix was confirmed on glibc and cherry-picked; the backend lane landed `--build-report-deps` and the native-support unit. Handoff at the top of this document.
- `B4` and `B7` merged: `goose build --units` with the object store, link skip, no-op short-circuit, `--rebuild` and `--verify-reuse`; the IR pipeline writes units through the same assembler (52 of 56 pilot fixtures build and run from IR units; legacy unit output unchanged). **`G-UNITS` holds for its structural gates on the synthetic family and its theorem (`TH-REUSE-01`)**; its Aincrad3 table exists only for a smaller entry point (§11.3), because the core entry cannot build in units mode until `B8`.
- Review fixes merged (`R1`): the validator accepts mutable slices over `let` arrays, writable references where read-only ones are expected, and calls to functions that never return; loop variables are numbered as the encoding says; the trivially true corollary is gone and `validated_run_keeps_globals_typed` and `noReturn_sound` are added; 81 theorems audited, the safety statement unchanged. Corpus conformance: 72 agree of 74 exported, with one exporter defect left (a result declared writable when a path returns read-only) and one fuel-bound program.
- `S3` part 2 merged: the harness has a corpus mode over every repository fixture and sample. Today the pilot profile reaches 75 of 580 programs (13%); 70 agree, 4 mismatch (the review's four, all open with their owners), 1 inconclusive (unbounded recursion runs out of fuel). The IR pipeline shows the same four. What keeps the other 504 out, by first unsupported feature: structs 151, string values 42, stored references 40, grow-shrink arrays 36, `extern fn` 29, floats 27, variable arrays 26, ADTs 22, pools 19. Flat structs are in `core-shrink`, so `S8` should take them first.
- Independent review merged (`semantics/review.json`, 17 entries over the 77 audited theorems outside the IR): 14 sound and meaningful, 2 weaker than claimed, 1 vacuous in part, none wrong. No fourth unsoundness in the safety theorem after 21 hand-built modules and about 27,300 structure-aware mutants; the tool runs exactly the audited `eval` and `validate`. Findings acted on: (1) `fault` is memory safety, not type safety — an unvalidated module can store a `bool` in an `i64` variable without faulting, the typed-store property is in `validated_steps_keep_invariant`, and mutability has no theorem; the claim ledger must say so; (2) `validate` rejects four of 82 repository programs the exporter accepts — a mutable slice over a `let` array, a call to an always-exiting function, a mutable reference bound to a `const` one, and one program the exporter should not have exported — and numbers a range loop's variable after its bounds where the encoding numbers it before; (3) `validated_run_keeps_live_refs` is trivially true as stated; (4) the bitwise theorems prove range only; (5) coverage rows lack evidence and limits. Each is assigned below.
- **`G-PILOT` reached.** Its last piece, the seeded fuzz gate runs against the Lean model, completed: `scalar` 2000 of 2000 agree, `numeric` 2000 of 2000 agree, no failure, no unsupported case. (`order` joins when `S4` reaches the exporter.)
- Earlier S4 Lean milestone (superseded by the completion entry above): a by-reference parameter whose pointee is a slice validated with content roots in the annotation, and `validated_never_faults` kept its statement. At that point exporter and GIR support were still pending; those follow-ups are recorded as integrated in the later S4 entries.
- `S6` merged: `--pipeline gir` builds and runs pilot programs through GIR-L and its own C emitter. On the merged tree the conformance harness through the IR backend gives 54 agree, 0 mismatch, 4 unsupported (native `-O0` and `-O2`, and the JIT); the lane's legacy-versus-IR differential is identical on 324 comparisons including abort file and line, and its three-oracle fuzz runs (300 seeds) show no disagreement on `scalar` and `numeric`. Full suite green, default output equal on 1,232 emissions. `G-GIR` now waits only on its theorems (`T3`) and the rest of the negative matrix (`H1`). Known gaps: any function in a call cycle that owns a grow-only slot is rejected (`recursive-resizable`), more conservative than the legacy backend; legacy optimizer results feed `--specs` and BCE analysis when those reports are requested. Under `--pipeline gir --stacks`, the IR path returns before `CodeGen::StackReport`, so no stack report is produced. "An element region tops its stack for its whole life" is not yet a verifier rule.
- `H3` in part, merged: `test/scale/lint_parity.py` compares candidate and reference byte for byte over 296 lint runs (26 inputs, 23 option sets), 23 facts streams including `compiler_revision`, and 64 `--check` runs: no difference. `specialization_fanout` still counts checked contexts: on a generated program the linter reports 152 checked specializations and the report 152 entry-reachable contexts, while emitted bodies go from 145 to 37 with `--share`. `lint` is dispatched before any flag parsing and never constructs an optimizer, code generator or report; the linter suite and the facts-scale case pass with Lean absent from `PATH`. `LINT-07` (a units-built companion) waits for `B4`.
- `T1`, second attempt, merged: **`TH-SAFE-01` is proved**: `validated_never_faults : validate m = ok → ∀ fuel profile kind, eval fuel profile m ≠ fault kind`, audited, with `TH-MEM-02` (`validated_steps_keep_invariant`) and `TH-CORE-01` (`validated_context_sound`, a semantic property of contexts, not a separate static judgment). The proof found the validator unsound in three ways and fixed each by rejecting more: a global initializer dereferencing a returned reference to a later global; a callee reading a later global hidden under a parameter's summary entry; a summary entry for a parameter that does not exist. The by-value loop read the IR lane reported is fixed too. 80 theorems audited; pilot harness unchanged (54 agree, 4 unsupported). The evaluator was not changed. `G-PILOT` holds on the proof side; its two 2000-case fuzz runs are in progress.
- `T3`, first attempt, merged: the lowering theorem holds as an audited theorem only for a straight-line fragment (all expressions without short-circuit, if- and block-expressions and calls; `let`, assignment, rebind, append, print), under a decidable fragment predicate. The IR validator's soundness is proved for terminators, operand typing, origins and summaries, and scalar operations are shown never to fault; dominance and scope balance are not yet shown to follow from acceptance. Control flow, loops and calls remain. A mutation of the lowering (sampling a view after its index expression) is caught by `agree` on the `sampled_extent` golden. `G-GIR` not reached; second attempt launched.
- `B6` merged: each checked context's dependencies and a result digest are recorded under the report flag, and a predictor compares two reports. Shadow result: no under-approximation over 41 source edits forwards and backwards, a seeded 40-step random sequence and about 7,000 one-token mutants of repository fixtures; 247 contexts predicted against 222 changed. Nothing reuses the record. Known not recorded: facts flowing back from call sites, optimizer reads, shader include files, global initialization order; and results of functions reading reference-holding globals depend on checking order, which only a recheck confirms. These are the prerequisites deferral `X2` has to close.
- `S5` merged: the compiler lowers its Core to GIR-H, verifies it, and writes it with `--emit-gir-high`. On the merged tree all 54 exporting pilot programs are byte-identical to the Lean reference lowering and agree with Core; the lane reports the same for 300 seeds each of `scalar` and `numeric`. Nine verifier rejections are unit-tested.
- `B3` merged: `--emit-units` writes a program as translation units. On the merged tree: 575 of 630 corpus programs build from units and behave as expected (55 skipped for native layers, none failing), every locality case passes, default output equals the reference on 1,232 emissions, the full suite is green. Aincrad3 at `-O1 --share` emits as 442 units, median 48 KB, largest 1.2 MB; but the units total 67 MB against 47 MB for the same program as one file, so per-unit declarations and preludes add about 40%. That overhead is cold-build cost and goes to `O3`.
- `U1`, first defect: the two baseline reds are a genuine runtime defect. On musl the main thread's native stack range comes back as only what is mapped so far, so a real overflow falls outside it and the diagnostic is never printed. Fix `7cd7526` on branch `upstream-pr/native-stack-bounds-main-thread-musl` (from upstream `master`), cherry-picked here as `2de048a`. The baseline suite is now fully green on this host. Verified on Alpine in Docker (base fails with status 139, fix prints the diagnostic) and on Debian sid with Clang 23.1.3 and GCC 16.2.0 (unchanged). The draft pull request is not opened yet: the before/after measurement the guidelines require needs a quiet host, and the fix branch has to be pushed to the fork before the exact Docker reproducer can be run.
- `S7` merged: Lean GIR-H with its interpreter, validator, decoder and writer, the reference lowering, the `gir-h/0.2` tag table (specification §12.2), 26 goldens and 37 invalid modules. The compiler's own exports of 52 pilot programs lower and agree between Core and GIR-H.
- `T1`, first attempt: `TH-FUEL-01` and `TH-MEM-01` audited; `TH-MEM-02` only per memory operation; `TH-CORE-01` only for the entry's shape; `TH-SAFE-01` not proved. `G-PILOT` not reached. The lane changed `Val.resizable` to carry its element type, which broke the sharing proofs; they are being repaired before either merges.
- `T2` merged: `TH-ERASE-01`, `TH-SHARE-01`, `TH-SHARE-02`, `TH-REUSE-01` and the quotient checker's soundness pass the audit (58 theorems audited in all, three allowed axioms only). **`G-SHARE` reached.** The proved quotient renames contexts per implementation rather than implementation indices, because bodies name contexts; it does not claim the shared module itself validates, only that it never faults when the unshared one does not.
- `S2` follow-up merged: exporter and validator agree on all pilot fixtures (54 agree, 4 unsupported, 0 mismatch); 300 seeded cases each of `scalar` and `numeric` agree; `order` is 298 of 300 unsupported until `S4`.
- `B2` merged: shared implementations and the stable naming seam in the legacy backend. `G-SHARE` holds except for its theorems, which lane `sem-share` is proving. Measurements in §11.2.
- Upstream `1cfe4b6` (three commits, including the relative-reference null test fix and extern type emission) merged into the branch without touching running lanes. On the merged tree: baseline suite shows only the two known reds, linter suite passes, default output equals master-plus-upstream on 1,232 emissions.
- `S2` merged: `--emit-core` reproduces the three goldens byte for byte. First run of the real harness: 49 fixtures agree, 8 mismatch, 1 unsupported; `scalar` and `numeric` fuzz lanes agree on 60 of 60. The mismatches are two disagreements between exporter and validator (what counts as a read in a summary; references to slice variables), sent back to the exporter lane.
- `S1` merged: Lean Core for the pilot (decoder, interpreter, validator, `run` and `validate`); goldens agree in both numeric profiles; 39 malformed and rejected fixtures.
- `B1` merged; `G-ATTR` reached except for budget freezing, which waits for a quiet host. First Aincrad3 attribution in §11.1.
- `T0` merged: 41 numeric theorems pass the audit; 1,224 generated cases agree with the base compiler in release and debug.
- `B5` part 1 merged: findings on what multiplies specializations (`test/scale/README.md`), the synthetic family, 16 source-edit cases passing on the single-file path.
- `S3` part 1 merged: 54 runnable pilot fixtures and 7 rejections passing on the legacy pipeline; harness and fuzz-driver stages tested against fake tools only.
- `G0` merged: runner filter and extra-argument option; default log identical to the old runner's; baseline status recorded in §3.
- `G1` merged: Lake project with a build-time axiom audit, the `goose-core/0.2` tag table (specification §12.1), three goldens. P0 complete.
- `G2` merged: `test/scale/gen.py` (issue #9's program, parameterized) and `test/scale/parity.py` (1,120 emissions compared; base against itself equal, `--no-bce` differs in 696).

- **Resumed 2026-10-14 on `master`.** The local `master` was fast-forwarded from `62366eb4` to `d440b9ab`, the former `goose-ir` tip (423 commits; no divergence). The `goose-ir` and `origin/goose-ir` refs were left unchanged, and no push was run. Continue with O3; prior post-run host-load failure invalidated its timing, so no budget is frozen.

- **Paused after rebase 2026-10-14.** Rebased `master` onto upstream `46356c26a94f0e1723b3b61ad56b93a7da70878f`, preserving fork tooling and the frozen campaign with integration corrections folded into replayed commits. Rechecked 67 unmerged refs, 29 clean in-repo lane worktrees and 12 preserved external worktrees (six dirty); no lane was started or integrated. Debug build and focused integration checks passed, including the corrected native/display reader exemptions and obsolete write allowance. Replaced the stale handoff with the branch-by-branch paused handoff and rehearsed its inspection commands in a clean environment. Strict path audit cannot pass because of the preserved external worktrees; privileged cron and `at` inspection remains incomplete. O3 still has no valid timing result; no measurements or pushes were run by this executor.

- **Paused 2026-10-14 after requested winddown.** Integrated accepted startup/block composition and checked construction exit, adaptation, allocation and trace-prefix stages. Focused Lake closures, 14 units tests, 30 runner self-tests and six local axiom checks passed. Committed incomplete lane edits, deleted 25 integrated refs, preserved 43 archive tags, removed obsolete checkouts and scratch, and retained nine clean caches under ignored `.work`. The handoff names every unmerged ref and reproduces inspection in a clean environment. Full lowering, construction, production BCE, H2 and final performance gates remain open. No push.

## 14. For the owner afterwards

- A confirmed linter inconsistency, not changed here because linter behaviour is frozen for the campaign: `redundant_cast` warnings carry an empty specialization list where `docs/lint/facts-v1.md` describes contexts. Minimal input in §12. Either the documentation or the producer should change, on the fork.
- Upstream draft pull requests owed under O7 and deferred by O8, each with its branch and drafted description: (1) `upstream-pr/native-stack-bounds-main-thread-musl`, commit `7cd7526`, committed description at `docs/design/upstream-drafts/native-stack-bounds-main-thread-musl.md` — still owed: the before/after `test/goose_in_goose` and normal-workload measurement on a quiet host, pushing the branch to the fork, running the exact Docker reproducer against the pushed commit, opening the draft. Note for the description: GCC 16.2 on musl could not be run; the musl results use GCC 15.2.
- The native-package rebuild draft is committed at `docs/design/upstream-drafts/native-package-rebuild-stamp.md`, on branch `upstream-pr/native-package-rebuild-stamp`. Upstream `c57587a1` and later native-build changes supersede its implementation; reassess its disposition before any external action.
- §11's attribution: whether the frontend or native compilation dominates Aincrad3's loop decides whether `X1` and `X2` are the next campaign.
- §8 and `semantics/decisions.md`: every contract change and every disagreement with the legacy compiler.
- `semantics/coverage.json`: theorems passing, parked, and the reviewer's answers.
- Whether to make units or sharing the default (`X4`), and whether to wire the Lean build and the scale harness into CI (P13).
- Parked items, each with its finding and branch.
