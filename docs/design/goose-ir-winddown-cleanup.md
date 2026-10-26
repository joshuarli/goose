# Goose IR winddown disk cleanup

## Winddown on 2026-10-26

The current accepted source checkpoint is `0df2c602` on `goose-ir`. All campaign lanes stopped. The current handoff is at the top of [the campaign document](goose-ir-campaign.md).

Twenty-two inactive campaign checkouts were retired after checking committed source, cleanliness, process ownership and ignored artifacts. All branch refs remain. The allocation lane's distinct history contains changes already integrated with the current world contract. The old exit lane's refined-integer rejection is already present in the compiler and regression script. The earlier `campaign/lean435` implementation is a parked historical model, not a candidate to replay over current sources.

`campaign/afk-family` at `81ffccd6` preserves the conditional family and Boolean case. Its owning receipts are underconstrained and have no accepted-program preservation proof. `campaign/afk-construction` at `881f7635` preserves those draft receipts. `campaign/afk-construction-receipts-draft` at `21a33526` preserves the obsolete earlier family snapshot. These drafts were deliberately excluded from `goose-ir`.

Useful evidence was compressed and checked with zstd integrity and a streamed tar listing before the source directories were removed. The current archives are under `.work/archive/winddown-2026-10-26/`: `resume-lean435-worktmp.tar.zst`, `close-resume-evidence.tar.zst`, `afk-evidence.tar.zst`, `close-units-logs.tar.zst`, `top-level-old-evidence.tar.zst`, `resource-run-evidence.tar.zst`, and `legacy-run-results.tar.zst`. The older 9.3 GB winddown archive is preserved as `.work/archive/winddown-2026-10-18.tar.zst` (about 432 MB). Reproducible old build caches, generated C, objects and completed run outputs were removed after preserving useful logs and inputs. Archive contents retain their original relative paths; historical receipts below may name locations now held only inside those archives.

The owner approved relocating the two external Aincrad checkouts into this repository's `.work/wt/`. The immutable `goose-master-2ad09c99` baseline remains there. Concurrent owner work committed the other experiment's runtime edits at `85fd984f` on `fix/linux-current-whole-region-advice-20261023` and retired that checkout. No changes from that experiment were merged into `goose-ir` by this winddown.

### Retained unmerged refs

The following refs are frozen snapshots or owner-managed work. A different branch history does not prove its patch is missing from `goose-ir`; many lane changes were cherry-picked or adapted. Only the three draft refs above are current parked proof designs. Inspect specific source differences and prerequisites before selecting any historical snapshot. No branch was deleted or automatically replayed during this winddown.

```text
backup/master-before-upstream-20261010
bookkeeping/gs-003-diverging-dead-code/base
bookkeeping/gs-004-default-init-order/base
campaign/accelerate-closing-record
campaign/accelerate-flow-produce
campaign/accelerate-gir-parity
campaign/accelerate-joint-args
campaign/accelerate-loop-preflight
campaign/accelerate-native-current
campaign/accelerate-perf-baseline
campaign/accelerate-perf-candidate
campaign/accelerate-ready-read-expressions
campaign/accelerate-ready-read-statements
campaign/accelerate-runtime435
campaign/accelerate-touch-call
campaign/accelerate-touch-ops
campaign/accelerate-typed-lineage
campaign/afk-allocation
campaign/afk-construct-roots
campaign/afk-construction
campaign/afk-construction-receipts-draft
campaign/afk-demand
campaign/afk-element-write
campaign/afk-exit
campaign/afk-family
campaign/afk-fixed-bytes
campaign/afk-report-trial
campaign/afk-short-circuit
campaign/assigned-origins
campaign/call-observed-captured
campaign/call-transport-policy
campaign/canonical-call-regions
campaign/channel-provenance
campaign/channel-renew-transport
campaign/close-alias-mutability
campaign/close-conformance
campaign/close-construction
campaign/close-demand
campaign/close-demand-bridge
campaign/close-demand-universal
campaign/close-exit
campaign/close-gir-units
campaign/close-once
campaign/close-once-replay
campaign/close-paranoid
campaign/close-receive
campaign/close-report-cost
campaign/close-translation
campaign/compiler-closing
campaign/construction-accepted-typing
campaign/construction-delivery
campaign/construction-flow-frame
campaign/construction-flow-values
campaign/construction-no-grow
campaign/construction-no-jump
campaign/construction-output-handoff
campaign/construction-query-source
campaign/consumed-access
campaign/consumed-arguments
campaign/consumed-control
campaign/consumed-mutations
campaign/cpp-closing
campaign/discharge-fixed-call
campaign/feature-limited-cap
campaign/feature-parameter-prologue
campaign/feature-reference-capture
campaign/fixed-call-low
campaign/flow-value-block-proof
campaign/inline-result-types
campaign/lean435
campaign/native-regions-aligned
campaign/occurrence-access
campaign/occurrence-api
campaign/occurrence-closing
campaign/occurrence-control
campaign/occurrence-lists_calls
campaign/occurrence-mutations
campaign/occurrence-scalars
campaign/ownership-landing-raw-roles
campaign/ownership-named-source
campaign/ready-control
campaign/ready-read-recorder
campaign/receiving-scope-context
campaign/resume-activation-projection
campaign/resume-call-contents
campaign/resume-call-footprint
campaign/resume-call-summary
campaign/resume-caller-alias-integration
campaign/resume-candidate-integration
campaign/resume-canonical-controls
campaign/resume-canonical-ordinary
campaign/resume-exit-cleanup-frames
campaign/resume-exit-let-build
campaign/resume-exit-producers
campaign/resume-exit-statements
campaign/resume-exit-values
campaign/resume-exit435
campaign/resume-fill-validation
campaign/resume-gir-model-integration
campaign/resume-ownership-builders
campaign/resume-ownership-cleanup
campaign/resume-ownership-contract
campaign/resume-ownership-statements
campaign/resume-ownership-value-effects
campaign/resume-ownership-values
campaign/resume-ownership-writes
campaign/resume-owning-evaluator
campaign/resume-projection-statements
campaign/resume-reservation-instances
campaign/resume-touch-classifier
campaign/resume-validation435
campaign/resume-writer-induction
campaign/resume-writer-ledger
campaign/root-recipe-bounds
campaign/runtime-closing
campaign/runtime-identities
campaign/simulation-consumer
campaign/source-canonical-facts
campaign/source-canonical-root-floors
campaign/source-closing
campaign/source-value-shapes-read-recipes
campaign/source-value-shapes-recipes
campaign/source-value-type-shapes
campaign/typed-recipe-tail
campaign/winddown-source-exit-refinements
campaign/winddown-source-outside-v4
campaign/winddown-source-ownership-builders
campaign/winddown-source-ownership-call-all
campaign/winddown-source-ownership-cleanup
campaign/winddown-source-ownership-core16
campaign/winddown-source-ownership-main
campaign/winddown-source-ownership-values
campaign/winddown-source-ownership-writes
campaign/winddown-source-root-authority
fix/codegen-local-name-cursor-rfc9-fork
fix/gs-002-callee-local-provenance
fix/gs-003-diverging-dead-code
fix/gs-004-default-init-order
fix/lint-facts-limit-512mib
fix/linux-current-whole-region-advice-20261023
fix/linux-whole-region-advice
fix/linux-whole-region-master
fix/linux-whole-region-nohuge-20261023
goose-ir-finish-construct-backend
goose-ir-finish-construct-core
goose-ir-finish-construct-execution-proofs
goose-ir-finish-construct-gir
goose-ir-finish-lower
goose-ir-finish-lower-call
goose-ir-finish-lower-each
goose-ir-finish-lower-source-contexts
goose-ir-finish-lower-validation
goose-ir-finish-perf-base
goose-ir-parity-base
goose-ir-resume-call-content-flow
goose-ir-resume-cfg
goose-ir-resume-closure-loop
goose-ir-resume-completion-lifecycle
goose-ir-resume-construction-ownership
goose-ir-resume-construction-wire-docs
goose-ir-resume-content-flow-source-proof
goose-ir-resume-context-lowering
goose-ir-resume-cpp-integrate
goose-ir-resume-destination-protocol
goose-ir-resume-dominance
goose-ir-resume-each-prefix
goose-ir-resume-emission-metadata
goose-ir-resume-emitted-typing
goose-ir-resume-empty-content-parity
goose-ir-resume-execution-begins
goose-ir-resume-execution-prefix
goose-ir-resume-expression-contents
goose-ir-resume-expression-typing
goose-ir-resume-fixture-typing
goose-ir-resume-frag-equations
goose-ir-resume-frame-migration
goose-ir-resume-fuel-bound
goose-ir-resume-fuel-control
goose-ir-resume-fuel-control-blocks
goose-ir-resume-fuel-control-branches
goose-ir-resume-fuel-control-range
goose-ir-resume-fuel-expressions
goose-ir-resume-fuel-mutations
goose-ir-resume-fuel-statements
goose-ir-resume-global-control
goose-ir-resume-global-read
goose-ir-resume-interrupted-regressions
goose-ir-resume-join-contents
goose-ir-resume-metadata-control
goose-ir-resume-metadata-each
goose-ir-resume-metadata-profile
goose-ir-resume-named-reservation-proofs
goose-ir-resume-native-check
goose-ir-resume-native-integrate
goose-ir-resume-native-trace
goose-ir-resume-ownership-cancel-source
goose-ir-resume-ownership-design
goose-ir-resume-permission-control
goose-ir-resume-permission-control-graph
goose-ir-resume-permission-control-scopes
goose-ir-resume-permission-induction
goose-ir-resume-permission-preservation
goose-ir-resume-permission-references
goose-ir-resume-permission-storage
goose-ir-resume-print-sources
goose-ir-resume-progress-verifier
goose-ir-resume-protocol-attach
goose-ir-resume-protocol-exit-landing
goose-ir-resume-protocol-open
goose-ir-resume-protocol-publish
goose-ir-resume-protocol-writes
goose-ir-resume-provenance-convergence
goose-ir-resume-range-execution
goose-ir-resume-range-sources
goose-ir-resume-receiving-lifecycle
goose-ir-resume-reflection-blocks
goose-ir-resume-reflection-leaves
goose-ir-resume-reflection-output
goose-ir-resume-reflection-places
goose-ir-resume-renewal-prefix
goose-ir-resume-replacement-demand
goose-ir-resume-replacement-sites
goose-ir-resume-reservation-cap-begins
goose-ir-resume-result-origins
goose-ir-resume-returnfree-typing
goose-ir-resume-runtime-check
goose-ir-resume-runtime-integrate
goose-ir-resume-runtime-lifecycle
goose-ir-resume-runtime-union-check
goose-ir-resume-scope-migration
goose-ir-resume-scopes
goose-ir-resume-semantic-check2
goose-ir-resume-snapshot-control
goose-ir-resume-source-root-bounds
goose-ir-resume-source-statement-typing
goose-ir-resume-source-symbols
goose-ir-resume-storage-source
goose-ir-resume-storage-walk
goose-ir-resume-storage-walk-loops
goose-ir-resume-summary
goose-ir-resume-summary-mutations
goose-ir-resume-target-frames
goose-ir-resume-trace-fixtures
goose-ir-resume-typed-fixtures
goose-ir-resume-validation
goose-ir-resume-whole-replacement
goose-ir-source-ready-seeds
goose-ir-source-root-ceilings
goose-ir-view-source-only
master
perf/rfc9-bce-upstream-qualification
refresh/upstream-20261023
resume-carried-named-fix
resume-kernel-numeric-review
resume-root-authority-contract
resume-summary-abort-parity
review/cached-callee-references
review/pr18-latest
review/reordered-reference-fields
upstream-pr/cached-callee-references
upstream-pr/gs-004-reordered-reference-initializers
upstream-pr/native-package-rebuild-stamp
upstream-pr/native-stack-bounds-main-thread-musl
upstream-pr/reordered-reference-fields
```

## Historical cleanup record from 2026-10-14

The final cleanup ran on 2026-10-14. No active process referenced the six dirty sibling worktrees before archival.

After archive cleanup, `df -h .` showed 206.7 GB free and `.work` used 9.0 GB. A later shared-filesystem check showed 205.7 GB free. The initial check showed 74.2 GB free and 23.2 GB in `.work`. The first cleanup check showed 75.7 GB free and 21.9 GB in `.work`; later campaign cleanup changed the shared filesystem totals.

## Removed clean worktrees and scratch

Removed these four clean registered worktrees with `git worktree remove`. Their original branch refs remain unchanged.

- `../goose-lint-aincrad-20261011` at `0c127337`, branch `fix/lint-facts-limit-512mib`.
- `../goose-update-latest-20261011` at `ad8f2a87`, branch `qualify/upstream-fee060c-20261011`.
- `../goose-upstream-pr-generic-argument-backtracking` at `b37cebb7`, branch `upstream-pr/generic-argument-backtracking`.
- `../goose-upstream-pr-gs-004-reordered-reference-initializers` at `81004d20`, branch `upstream-pr/gs-004-reordered-reference-initializers`.

Removed temporary performance and build artifacts from `.work/tmp`: `o3-20261014`, `wide-gir-units-corpus-fixed`, `wide-gir-units-corpus`, `h2-random-snapshot-seed-1`, `h2-random-seed-1`, `campaign-wide-goose`, and `cckLKoIj.s`. The O3 timing was invalidated by the campaign handoff, so these outputs were not needed to resume the campaign.

## Archived dirty sibling worktrees

Each dirty checkout was committed on a new local archive branch before removal. Original named refs remain at their old heads. The two detached tips are the parents of their archive commits. Each commit records frozen evidence that is unverified and is not a merge candidate.

- `../goose-emitted-body-diagnostics`: old `experiment/emitted-body-diagnostics` at `6be31c0c`; archive `archive/winddown-20261014-emitted-body-diagnostics` at `6f62bfe9`.
- `../goose-rfc9-bce`: old `perf/rfc9-bce-upstream-qualification` at `23366273`; archive `archive/winddown-20261014-rfc9-bce` at `089c75d3`.
- `../goose-rfc9-forkcursor`: old `fix/codegen-local-name-cursor-rfc9-fork` at `54f1a765`; archive `archive/winddown-20261014-rfc9-forkcursor` at `60f6a767`.
- `../goose-rfc9-namecursor`: old `perf/codegen-local-name-cursor-rfc9` at `2e7ee8ff`; archive `archive/winddown-20261014-rfc9-namecursor` at `dd4dadcb`.
- `../goose-rfc9-profile`: detached at `a03a2ca6`; archive `archive/winddown-20261014-rfc9-profile` at `d6b3ca40`.
- `../goose-rfc9-upstream-base32`: detached at `32f8ff87`; archive `archive/winddown-20261014-rfc9-upstream-base32` at `57686bd4`.

Converted the six archive branches above and `archive/winddown-20261014-validation-scratch` to lightweight tags with the same names and target commits. The original source branches remain at their old heads.

Removed the emitted-body-diagnostics, forkcursor, profile, and upstream-base32 checkout directories. `git worktree remove` deregistered the bce and namecursor worktrees but could not delete their root-owned build outputs. Their unregistered partial directories remain at `../goose-rfc9-bce` (62.5 MB) and `../goose-rfc9-namecursor` (228.4 MB). Each `checks/gcc16-compiler` tree has 12.1 MB of root-owned outputs: `CMakeFiles/`, `tcc/`, `.cmake/`, `tcclib/`, `generated/`, `libgoose_shaderc.a`, `build.ninja`, `.ninja_log`, `cmake_install.cmake`, `goose`, `.ninja_deps`, and `CMakeCache.txt`. No privilege override was used.

## Preserved paths

Preserved `../goose-rfc9-gig-perf-20261011` (115.7 MB). It is not a registered worktree and contains C inputs, result data, scripts, and draft PR text.

Removed the obsolete 560 MB copied validation tree after checking its source against reachable local Git history. Its one unique older execution-check snapshot is preserved by the lightweight tag `archive/winddown-20261014-validation-scratch` (`20ba2324`), in `semantics/Goose/Construct/ExecutionChecks.lean`; it is unverified evidence, not a merge candidate. The temporary decoder wrapper referenced disposable generated input and is superseded by committed source fixtures.

Removed 49 clean inactive campaign checkouts in the first pass, then five completed finish, staging, and cleanup checkouts. Deleted the fully merged integration-staging branch and the ancestry-merged `goose-ir-finish-construct-native-glue` branch.

Deleted 24 inactive branches whose branch-only commits all have patch-equivalent commits in `master` and contain no branch-only merges:

- `bookkeeping/gs-002-callee-local-provenance/base`
- `goose-ir-finish-cfg-validation`
- `goose-ir-finish-construct-validation`
- `goose-ir-finish-core-declarative-demand`
- `goose-ir-finish-core-declarative-roots`
- `goose-ir-finish-core-declarative-tables`
- `goose-ir-finish-core-metadata`
- `goose-ir-finish-dominance`
- `goose-ir-finish-h2`
- `goose-ir-finish-lower-eventual`
- `goose-ir-finish-provenance`
- `goose-ir-finish-runtime-typing`
- `goose-ir-finish-shrink-qualification`
- `goose-ir-finish-source-divergence`
- `goose-ir-resume-core`
- `perf/codegen-local-name-cursor-rfc9`
- `review/diverging-dead-code`
- `review/parse-int-overflow`
- `upstream-pr/basecase-reference-alias`
- `upstream-pr/diverging-dead-code`
- `upstream-pr/generic-argument-backtracking`
- `upstream-pr/parse-float-leading-zeroes`
- `upstream-pr/parse-int-overflow`
- `upstream-pr/serialized-offset-overflow`

Retired 32 parked historical S8 branch refs as lightweight tags under `archive/retired/`. Each tag points directly to the original commit, so its full history remains reachable. This preserves the parked candidates without claiming their changes are merged.

| Former branch | Retained tag |
| --- | --- |
| `campaign/s8-argument-root-syntax` | `archive/retired/campaign/s8-argument-root-syntax` |
| `campaign/s8-call-effect-bridge` | `archive/retired/campaign/s8-call-effect-bridge` |
| `campaign/s8-expr-final` | `archive/retired/campaign/s8-expr-final` |
| `campaign/s8-global-domain` | `archive/retired/campaign/s8-global-domain` |
| `campaign/s8-loop-final` | `archive/retired/campaign/s8-loop-final` |
| `campaign/s8-loop-owner-final` | `archive/retired/campaign/s8-loop-owner-final` |
| `campaign/s8-lower-helper-wip` | `archive/retired/campaign/s8-lower-helper-wip` |
| `campaign/s8-owner-authority` | `archive/retired/campaign/s8-owner-authority` |
| `campaign/s8-owner-call-args` | `archive/retired/campaign/s8-owner-call-args` |
| `campaign/s8-place-final` | `archive/retired/campaign/s8-place-final` |
| `campaign/s8-proof-composition` | `archive/retired/campaign/s8-proof-composition` |
| `campaign/s8-shrink-owner-contract` | `archive/retired/campaign/s8-shrink-owner-contract` |
| `campaign/s8-stmt-assign-whole` | `archive/retired/campaign/s8-stmt-assign-whole` |
| `campaign/s8-stmt-assignwhole-case-prep` | `archive/retired/campaign/s8-stmt-assignwhole-case-prep` |
| `campaign/s8-stmt-assignwhole-final` | `archive/retired/campaign/s8-stmt-assignwhole-final` |
| `campaign/s8-stmt-final` | `archive/retired/campaign/s8-stmt-final` |
| `campaign/s8-stmt-popn-clear` | `archive/retired/campaign/s8-stmt-popn-clear` |
| `campaign/s8-stmt-resize-main` | `archive/retired/campaign/s8-stmt-resize-main` |
| `campaign/s8-stmt-resize-next-wip` | `archive/retired/campaign/s8-stmt-resize-next-wip` |
| `campaign/s8-stmt-resize-wip` | `archive/retired/campaign/s8-stmt-resize-wip` |
| `campaign/whole-root-effect-footprint` | `archive/retired/campaign/whole-root-effect-footprint` |
| `goose-ir-s8-contract` | `archive/retired/goose-ir-s8-contract` |
| `goose-ir-s8-fixtures` | `archive/retired/goose-ir-s8-fixtures` |
| `goose-ir-s8-lower-next` | `archive/retired/goose-ir-s8-lower-next` |
| `goose-ir-s8-proof-block` | `archive/retired/goose-ir-s8-proof-block` |
| `goose-ir-s8-proof-call` | `archive/retired/goose-ir-s8-proof-call` |
| `goose-ir-s8-proof-expr` | `archive/retired/goose-ir-s8-proof-expr` |
| `goose-ir-s8-proof-foundation` | `archive/retired/goose-ir-s8-proof-foundation` |
| `goose-ir-s8-proof-stmt` | `archive/retired/goose-ir-s8-proof-stmt` |
| `goose-ir-s8-step-stmt` | `archive/retired/goose-ir-s8-step-stmt` |
| `goose-ir-s8-storage-foundation` | `archive/retired/goose-ir-s8-storage-foundation` |
| `goose-ir-sem-gir` | `archive/retired/goose-ir-sem-gir` |

Removed two clean inactive historical baseline checkouts after confirming their commits remain reachable and no process referenced their paths. Ten clean worktrees under `.work/wt` remain for baseline and expensive artifact reuse, named in the campaign handoff. No registered external worktree remains.

## Retired completed lane snapshots

Retired four more completed lane branches as same-tip lightweight tags under `archive/retired/`:

- `goose-ir-finish-construct-eval` at `9984015d`. Its evaluator, runtime, execution checks and runner source match master exactly.
- `goose-ir-finish-construct-native` at `aa922b6d`. Preserve the earlier Core-export integration snapshot.
- `goose-ir-finish-typing-validation` at `69fec42a`. Its typing-proof source matches master. Its older audit and coverage snapshot is superseded.
- `goose-ir-winddown-disk-cleanup` at `02e31ccc`. Preserve the earlier cleanup-document snapshot.

These tags preserve the full original histories. Retirement does not claim every historical patch is merged. The current unfinished compiler and proof lanes remain branches.

The cleanup leaves 37 unmerged branches: 11 current campaign lanes or baselines and 26 owner-managed refs. Twenty-five integrated branch refs were deleted. Forty-three archive tags preserve retired evidence and candidate histories.
