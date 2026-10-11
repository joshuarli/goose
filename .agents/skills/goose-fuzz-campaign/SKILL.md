---
name: goose-fuzz-campaign
description: Run a bounded Goose compiler fuzzing campaign, triage findings against the exact upstream revision, and turn independent confirmed bugs into reviewable fixes. Use for requests to start, resume, or expand Goose fuzzing and candidate discovery.
---

# Goose fuzz campaign

Read the repository `AGENTS.md` and `fuzz/README.md` before acting. Treat the
invocation as authorization to run local discovery, investigate findings, and
prepare local fixes. Preserve the user's existing authorization boundaries for
network access, pushes, pull requests, and other external changes.

## Define the session

Extract any requested time budget, target areas, candidate count, and expected
deliverables. When these are omitted, begin without asking: use a five-minute
discovery budget for each applicable lane, seek up to three independent strong
candidates, and prepare local patches only for findings that meet the candidate
bar below. Adjust the mix as early results justify; a time budget bounds new
campaign starts, while replay, reduction, and preserving evidence may finish
after it expires.

Record these two revisions separately:

- **Campaign revision:** the fork revision containing the fuzz infrastructure.
- **Target revision:** the exact current upstream revision against which a bug
  and its fix must be demonstrated.

Inspect current branches, worktrees, remotes, build artifacts, open findings,
and available toolchains before building. Reuse an artifact only when its
recorded source revision and flags match. Keep all seeds, commands, environment
identity, summaries, and failure artifacts under ignored build storage.

For a broad campaign, delegate independent ready lanes when subagents are
available. Give each lane an exclusive output directory and a bounded CPU and
memory budget. One coordinator owns deduplication, upstream confirmation,
candidate selection, and integration. Avoid concurrent builds that contend for
the same directory or exhaust the host.

## Run discovery

Build and run the repository's existing tools rather than creating a new
harness first:

1. Run `doctor` and `smoke` from `fuzz/driver.py` before longer semantic work.
2. Cover the `aggregate`, `numeric`, `order`, `resize`, `scalar`, and `trap`
   lanes with explicit seeds, bounded counts and duration, and the full Goose/C
   optimization matrix. Add `--sanitize` where its cost fits the session.
3. Run both native targets, `goose_fuzz_parser` and `goose_fuzz_pipeline`, with
   separate seeded corpora, artifact prefixes, timeouts, and total-time limits.
   Seed parser work from syntax fixtures and pipeline work from the checked-in
   native corpus plus small valid fixtures.
4. Run `bench/bce_fuzz.py` when optimizer and bounds-check behavior is in scope.

Campaign processes may share an immutable compiler build. They must not share
mutable corpus, scratch, or artifact paths. Save no-finding summaries as well as
failures so coverage of the session remains auditable.

## Triage every finding

Do not patch the campaign revision first. For each finding:

1. Replay it twice and preserve the original artifact.
2. Reduce it structurally with `fuzz/driver.py reduce` when it came from a
   semantic lane. Minimize native artifacts while preserving the same failure
   class and compiler stage.
3. Reproduce the minimized input on a clean build of the exact target revision.
   Discard fork-only failures and record flaky or unreproducible inputs.
4. Check repository history and current upstream issues and pull requests for a
   duplicate before selecting it.
5. Identify the violated language or compiler invariant and the root cause.
   Several symptoms from one cause count as one candidate.

A strong candidate has a deterministic upstream failure, a small legal input or
clearly invalid input that must be rejected, a specific observable expectation,
a plausible root cause, and a focused regression test. Rank correctness,
crashes, miscompilation, and broken diagnostics above speculative hardening or
inputs outside the language contract.

## Develop selected candidates

Use a separate worktree and branch from the exact target revision for each
independent fix. Keep fork fuzz tooling out of upstream fix branches.

Write the smallest regression test that fails before the fix, then repair the
root cause without weakening types, adding silent fallbacks, or widening the
contract. Preserve the layout of every existing `.goose` source and test file;
do not run `format_goose.py` on it. A newly added valid `.goose` test or
reproducer may be formatted and checked. Keep malformed parser fixtures exactly
as required by their diagnostic assertions.

Verify the narrow changed behavior first. Demonstrate the regression on the
exact unpatched target and the passing result on the fix with identical flags.
For pathological input or an allocation/performance-sensitive change, also run
the representative normal-workload measurements required by `AGENTS.md` before
recommending the patch. Use Clang 23 for final upstream-fix verification and
record compiler, libc, architecture, kernel, flags, sample count, variability,
and peak memory when relevant.

Prepare commits and concise draft material only to the extent requested. Follow
the repository's upstream title, description, Docker reproducer, and testing
rules. Do not push or open/update pull requests unless the user has explicitly
authorized that external action in the current conversation.

## Report the session

Report the campaign and target revisions, lanes and seeds, budgets and case
counts, sanitizer coverage, findings and disposition, selected independent
candidates, verification actually run, and remaining limits. Distinguish local
patches from externally published work. A no-finding run is a valid bounded
result; never inflate weak or duplicate findings to reach a candidate count.
