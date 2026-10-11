# Linter implementation decisions

## Frontend and side effects

`goose lint` uses the canonical C++ parser, resolver, and typechecker and stops
before optimization, generated C, JIT, or target execution. Parser spans and
comment metadata are captured only when lint asks for them. Existing compiler
warning text, ordering, and deduplication remain unchanged outside lint mode.
Imports use the normal resolver in offline mode; `--allow-fetch` explicitly
enables package fetching but never target execution.

Typechecking `embed_file` reads the named resource. Typechecking
`embed_shader` invokes the bundled in-process shader compiler and may read
shader include files relative to the shader. These operations do not execute
program code or modify the project. Their inputs are part of the source's
required analysis environment.

The facts producer and policy engine are separate executables built and
packaged beside `goose`. C++ exports typed primitives; the Goose companion
validates the complete facts stream, decides rules, applies groups, severity,
suppression and baseline policy, and renders text or JSONL. Missing companions,
malformed facts, and resource-limit failures are tool errors. Facts and output
use private temporary files with bounded size and cleanup.

## Facts and public output

The private bridge is [facts-v1.md](facts-v1.md). It uses strictly ordered
JSONL, deterministic stream IDs, source-relative display paths, source-content
hashes, FNV-1a64 integrity, and bounded record, stream, and record counts. The
checksum detects accidental corruption; it is not an authenticity check.
Records and references are validated before rule evaluation.

The public schema is [diagnostics-v1.md](diagnostics-v1.md). Suppressed and
baselined findings stay visible. Baselines fingerprint rule, path, message,
evidence, specialization context, and duplicate occurrence. Mutation is
explicit and atomic; stale entries are visible and separately selectable for
denial.

## Rule scope and coverage

All 12 required rule IDs are implemented for the documented proof shapes in
[rule-inventory.md](rule-inventory.md). This is deliberately narrower than a
general effect, alias, or control-flow analysis:

- Existing warnings retain the original compiler proofs and consensus policy;
  lint facts add stable codes, exact or honest line locations, and checked
  specialization contexts.
- `discarded_failure` and `unchecked_poll_result` use exact API identities and
  trailing status-result facts. Straight-line local reassignment identifies a
  result overwritten before inspection. Unknown result flow abstains.
- `unused_pure_value` reports only literal or constant integer-expression
  statements whose typed subtree is proven effect-free and nontrapping.
- The two `review` rules accept only their narrow typed, same-block shapes;
  other relations and dataflow abstain.
- The two `project` rules require exact API contracts and direct call/root
  identities. Contracts assign semantics; their presence does not prove that
  the implementation obeys those semantics.
- `specialization_fanout` reports proven entry-reachable specializations and
  discloses unknown reachability in coverage.

Coverage separates parsed sources from entry-reachable checked specializations
and reports uninstantiated generic bodies and unsupported reachability. A
missing project contract makes a selected project analysis incomplete. A clean
run does not establish that unsupported patterns are absent. The 53 remaining
Issue #10 candidates have explicit deferred reasons and promotion conditions;
they are not runnable rules.

## Compatibility and regression evidence

Typed warning codes are assigned at existing emission sites. Collection
follows warning hold/retry, quiet-mode, original-node deduplication, and cast
consensus. The lint-only metadata path remains dormant for ordinary compiler
commands. Warning parity, linter fixtures, JSONL validation, and the
Goose-in-Goose bootstrap are regression checks for these boundaries.
