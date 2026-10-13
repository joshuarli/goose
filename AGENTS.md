# Goose repository guide

## Commands

- Configure and build: `cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug && cmake --build build --target goose`.
- Run the baseline suite: `python test/run_tests.py --profile baseline --cc native --require-clang`.
- Check edits with `git diff --check`; use `python scripts/format_goose.py --check <files>` for newly added `.goose` files.

## Invariants

- Preserve existing `.goose` layout; do not format existing source or tests.
- Keep malformed parser fixtures in `test/errors/` byte-for-byte as authored.
- Never weaken or delete a test just to make a change pass.
- Use focused checks by default; widen verification only for a concrete integration risk.
- Keep code comments self-contained and useful without planning documents.
- Keep worktrees and scratch under ignored `.work/`; set `TMPDIR` to `.work/tmp` for commands that spill files.
- Follow [development and contribution conventions](docs/development.md); do not push.

## Topic map

- Language and users: [tutorial](docs/tutorial.md), [language specification](docs/goose_spec.md), [standard library](docs/stdlib.md), [package use](docs/packages.md), [samples](samples/README.md).
- Compiler and tests: [implementation](docs/implementation.md), [testing](docs/testing.md), [development](docs/development.md), [Goose in Goose](test/goose_in_goose/README.md), [scale tests](test/scale/README.md).
- Runtime and compiler design: [JIT](docs/design/jit_backend.md), [namespaces](docs/design/namespaces.md), [dynamic data](docs/design/owning_dynamic_data.md), [relative references](docs/design/relative_references.md), [serialization](docs/design/serialization.md), [SOA](docs/design/soa.md), [string constants](docs/design/string_constants.md), [stdlib design](docs/design/stdlib_design.md).
- Packages and analysis: [package design](docs/design/packages.md), [analysis inventory](docs/design/analysis_inventory.md).
- Goose IR: [specification](docs/design/goose-ir-spec.md), [validation](docs/design/goose-ir-validation.md), [campaign record](docs/design/goose-ir-campaign.md).
- Lint: [guide](docs/lint/README.md), [decisions](docs/lint/DECISIONS.md), [rule inventory](docs/lint/rule-inventory.md), [contracts](docs/lint/contracts-v1.md), [facts](docs/lint/facts-v1.md), [diagnostics](docs/lint/diagnostics-v1.md), [performance](docs/lint/performance.md), [older proposal](linter.md).
- Semantics records: [decisions](semantics/decisions.md), [trust boundary](semantics/trust.md).
- Benchmarks: [summary](bench/summary.md), [results](bench/results.md), [design](bench/design.md), [plan](bench/plan.md), [notes](bench/notes.md), [adoption](bench/adoption.md), [parser backtracking](bench/parser_backtracking.md), [Kostya workloads](bench/kostya/README.md).
- Tools and workflows: [fuzzing](fuzz/README.md), [VS Code](vscode/README.md), [upstream draft: package rebuild stamp](docs/design/upstream-drafts/native-package-rebuild-stamp.md), [upstream draft: native stack bounds](docs/design/upstream-drafts/native-stack-bounds-main-thread-musl.md).
