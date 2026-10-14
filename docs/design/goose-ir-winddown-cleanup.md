# Goose IR winddown disk cleanup

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
