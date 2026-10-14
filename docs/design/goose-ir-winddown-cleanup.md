# Goose IR winddown disk cleanup

On 2026-10-14, removed inactive campaign artifacts after confirming that no process used their paths. The four clean registered worktrees were removed with `git worktree remove`; their branch refs remain.

The filesystem reported 74.2 GB free before cleanup and 75.7 GB after. The Goose `.work` tree fell from 23.2 GB to 21.9 GB.

Removed registered worktrees:

- `../goose-lint-aincrad-20261011` at `0c127337`, branch `fix/lint-facts-limit-512mib`.
- `../goose-update-latest-20261011` at `ad8f2a87`, branch `qualify/upstream-fee060c-20261011`.
- `../goose-upstream-pr-generic-argument-backtracking` at `b37cebb7`, branch `upstream-pr/generic-argument-backtracking`.
- `../goose-upstream-pr-gs-004-reordered-reference-initializers` at `81004d20`, branch `upstream-pr/gs-004-reordered-reference-initializers`.

Removed temporary performance and build artifacts from `.work/tmp`: `o3-20261014`, `wide-gir-units-corpus-fixed`, `wide-gir-units-corpus`, `h2-random-snapshot-seed-1`, `h2-random-seed-1`, `campaign-wide-goose`, and `cckLKoIj.s`. The O3 timing had already been invalidated by the campaign handoff. This scratch output was not part of campaign continuation state.

Preserved six dirty sibling worktrees:

- `../goose-emitted-body-diagnostics`: untracked `measurements/`.
- `../goose-rfc9-bce`: untracked `build.log`, `checks/`, and `configure.log`.
- `../goose-rfc9-forkcursor`: untracked `checks/` and `configure.log`.
- `../goose-rfc9-namecursor`: untracked `build.log`, `checks/`, and `configure.log`.
- `../goose-rfc9-profile`: modified `src/clone.h`, `src/codegen_emit.h`, `src/main.cpp`, `src/optimize.h`, and `src/typecheck_calls.h`; untracked `build.log`, `configure.log`, `measurements/`, and `src/profile.h`.
- `../goose-rfc9-upstream-base32`: untracked `build.log` and `configure.log`.

These worktrees remain because their dirty measurement and check directories mix generated outputs with Goose reproducers, scripts, source edits, patches, and result logs. The six sibling status entries were preserved. Their untracked build and configure logs are 4 KB each.

Also preserved `../goose-rfc9-gig-perf-20261011` (116 MB). It is not a registered worktree and contains C inputs, result data, scripts, and draft PR text. Preserved `.work/tmp/construct-validation-src-20261014` because its 560 MB of contents may include unique source edits. Build caches under `.work/wt/verify`, `.work/wt/verify-construct`, and `finish-*` remain available for campaign checks.
