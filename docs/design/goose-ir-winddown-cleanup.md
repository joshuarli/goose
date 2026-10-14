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

Removed the emitted-body-diagnostics, forkcursor, profile, and upstream-base32 checkout directories. `git worktree remove` deregistered the bce and namecursor worktrees but could not delete their root-owned build outputs. Their unregistered partial directories remain at `../goose-rfc9-bce` (62.5 MB) and `../goose-rfc9-namecursor` (228.4 MB). Each `checks/gcc16-compiler` tree has 12.1 MB of root-owned outputs: `CMakeFiles/`, `tcc/`, `.cmake/`, `tcclib/`, `generated/`, `libgoose_shaderc.a`, `build.ninja`, `.ninja_log`, `cmake_install.cmake`, `goose`, `.ninja_deps`, and `CMakeCache.txt`. No privilege override was used.

## Preserved paths

Preserved `../goose-rfc9-gig-perf-20261011` (115.7 MB). It is not a registered worktree and contains C inputs, result data, scripts, and draft PR text.

Preserved `.work/tmp/construct-validation-src-20261014` because its 560 MB may include unique source edits. Build caches under `.work/wt/verify`, `.work/wt/verify-construct`, and `finish-*` remain available for campaign checks.
