# Campaign: Lean-backed Goose semantics, Goose IR, and build scalability

**Status:** resumed 2026-10-17 at the owner's request. Local implementation and verification are active. Pushes remain unauthorized.
**Branch:** `master`. **Upstream base:** `46356c26a94f0e1723b3b61ad56b93a7da70878f`.
**Contracts:** [specification](goose-ir-spec.md), [validation plan](goose-ir-validation.md).

## Current execution

The resumed compiler built in Debug mode. H2 recovery cases E11–E16 and the separate 60-step sequence with seed 1 passed at `f570b026`. E10 exposed a builder-test include failure and a raw filesystem probe that bypassed input recording; `c203aa9d` repairs both, and its focused compiler-unit checks passed. E10 is being checked again on the integrated compiler. These runs establish no performance result.

The argument-root proof module exceeded the 4 GiB Lean heap cap. Splitting root declarations from global-effect replay passed both modules under the original cap without changing the existing theorem conclusions; integrated as `67e984bb`. A separate thread-creation failure came from an 8 GiB virtual-address limit, which has been removed while retaining the Lean heap limit.

The construction GIR lane independently decoded, validated, re-encoded byte-for-byte, and executed raw-byte, source-values and source-exit fixtures using the rebuilt construction compiler. These are lane results pending integration and review. Native target handling, whole-profile proofs and the final gates remain open.

## Handoff for the next executor

**Resume:** "Resume the paused Goose IR campaign from docs/design/goose-ir-campaign.md. Finish the remaining gates unattended. Take recommended decisions by default." First run `git status --short --branch`. On an authorized resume, cancel campaign closeout before selecting work. Recreate a missing selected worktree under `.work/wt` from its named branch.

**State at pause:** The integration branch is `master`. The code checkpoint before this handoff is `a9d3c620`. Winddown started at `dffdf0c2` after the completed integration checkpoint `66b8cdcc`. No work is pushed.

This winddown integrated accepted callee sources, actual global-initializer and entry frames, and the typed block constructor. It also integrated source-versus-receiver exit ownership, exact producer counts, explicit receiving adaptation, producer normalization, and checked allocation and trace-prefix kernel frames. Four positive lowering fixture records now use recognized origin kinds. Their programs, assertions and source lines are unchanged.

The independent Core judgment now proves `validate m = .ok () → WellFormed m`, including unconditional origin validity. Adversarial review found no P1 or P2 defect. Its Audit registration and coverage entry were integrated on resume in `f6ef88c6`. The exact-source Audit closure passed before the later argument-root module split; the final executable audit remains open. The universal BCE replacement proof is merged. The last full executable audit checked 157 claims at `9e888683`; no fresh full audit of the current code is claimed.

**Known red:** Whole-profile lowering and validation preservation remain incomplete. The unmerged readonly-destination change `920c9e42` invalidates unrestricted legacy fragment claims. Replace those claims with accepted-state composition before integration. The construction whole-execution and exit gates remain incomplete.

At `66b8cdcc`, raw-byte high GIR rejects with `GIR-V060`. The source-values high GIR executes correctly but re-encoding changes its declared type table. Native exports of raw bytes and source values fail `GIR-V090` stack-header ownership. Source-exit high export fails return-descriptor matching. These source fixtures are committed at `test/semantics/golden/construction_raw_bytes.goose`, `test/semantics/sem_construction_source_values.goose`, and `test/semantics/sem_construction_source_exit.goose`. The paused branch does not claim these integration failures are fixed.

Production BCE qualification is also red. The seven fixtures on `goose-ir-finish-bce` export and independently validate, but the required guarded case emits zero proven indexes. Read that branch's `docs/design/goose-ir-bce-qualification.md` before changing certificate rules. H2 still needs final requalification. Final performance measurements and campaign-wide gates have not run. O2 remains unadmitted, and the earlier O3 timing was invalidated.

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

**H2 acceptance is parked, not complete.** The audited harness now checks stdout, observes actual publish and link interruption points, checks E16's intermediate build, and reports nonzero ordinary random builds as failures. A targeted E13 run passed both observed interruptions and clean-build recovery. The strengthened seeded sequence was not rerun within its three-attempt budget, so the historical 60-step result is not current evidence. E10's raw independent C flags, target-only, and runtime-text-only dimensions are structurally unavailable through the current compiler interface; the harness marks them `unavailable`, and an E10 run exits with `incomplete` instead of treating them as passes. H2 remains parked until those dimensions are covered or its acceptance contract is revised.

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
- The GIR-H wire encoding is defined by the Lean lane, and the Lean lowering's output for each Core golden is the golden the C++ lowering must reproduce byte for byte. One reference lowering makes the C++ lowering instance-checkable by comparison instead of only by behaviour.
- `V-ROOT` no longer requires a same-scope root to be declared first. The compiler accepts rebinding a reference to a later-declared variable of its own scope, and that is safe because a scope's variables end together; the stricter rule would have rejected valid programs for no safety gain.
- Unary minus on an unsigned type is a compile error in Goose. The numeric model keeps a total definition for it; the Lean validator rejects it under `V-TYPE`.
- The checker already groups roots into classes: one helper called with many distinct globals and many locals at different depths gets two specializations, not one per call site. The synthetic family therefore has to vary the dimensions that do multiply specializations; `B1`'s dimension attribution on Aincrad3 says which those are, and `B5` builds its members from that.

## 13. Campaign log

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
- `H2` is parked, not complete. The earlier units edit-matrix and seeded 60-step randomized run in §11.3 are historical results, not current gate evidence. The audited harness passed the targeted E13 interruption/recovery case, but the strengthened seeded sequence was not rerun within its three-attempt budget; E10's raw independent C flags, target-only, and runtime-text-only dimensions are structurally unavailable and marked `unavailable`, so H2 remains incomplete as detailed in §11.3.
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
