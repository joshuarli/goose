# Goose lint

`goose lint` parses, resolves, and typechecks with Goose's production C++
frontend, then asks the adjacent `goose-lint` executable to apply Goose-authored
rules to a private facts stream. It stops before optimization, generated C,
native compilation, JIT, or execution of the target program. The install and
package scripts ship both executables together.

```sh
goose lint src/main.goose
goose lint src/main.goose --format jsonl
goose lint src/main.goose --deny discarded_failure
goose lint src/main.goose --group performance
goose lint src/main.goose --baseline .goose-lint-baseline.json --write-baseline
goose lint src/main.goose --require-complete
```

Lint uses cached and local imports without network access. A missing remote
package is an input error; `--allow-fetch` explicitly enables normal package
fetching. This flag never enables target execution or source-defined sidecars.
`embed_file` reads its named resource during typechecking. `embed_shader` invokes
the compiler's in-process shader compiler and may read shader include files.
Those inputs are not executed or modified. `-O0`, `-O1`, and `-O2` select and
report the analysis profile; facts are collected before optimization.

## Rules and proof limits

The default groups are `existing`, `correctness`, and `suspicious`. The shipped
required rules are:

| Group | Rule | Supported proof |
|---|---|---|
| existing | `redundant_cast` | Existing typechecker proof and specialization consensus. |
| existing | `redundant_reference_marker` | Existing typed warning site; warning facts retain checked specialization contexts. |
| existing | `avoidable_reference_copy` | Existing typed warning site; warning facts retain checked specialization contexts. |
| correctness | `discarded_failure` | Exact `stdlib::parse_int` status result discarded, unreferenced, or overwritten before inspection in straight-line local code. |
| correctness | `unchecked_poll_result` | Exact `qpoll` received-status result discarded, unreferenced, or overwritten before inspection in straight-line local code. |
| suspicious | `unused_pure_value` | Standalone literal or constant integer expression proved effect-free and nontrapping. |
| correctness | `stale_suppression` | Malformed, unknown, duplicate, or unmatched lexer-recognized directive. |
| review | `post_overflow_guard` | Opt-in: adjacent signed add/sub assignment and the canonical comparison against its original left operand, with a typed nonnegative right operand. |
| review | `stale_slice_length` | Opt-in: same-block full slice capture, direct positive growth of the same array, then use of the captured slice at `array.len - 1`. |
| performance | `specialization_fanout` | Opt-in: two or more concrete specializations proven reachable from the selected entry. Reports type and root-depth contexts, not runtime cost. |
| project | `view_before_append_argument` | Opt-in: configured API roles prove a direct slice argument is evaluated before a nested same-owner append call, and the callee uses the view after append. |
| project | `foreign_container_index` | Opt-in: configured API roles prove a nested index-producing call uses a different direct local array than the consumer. |

`stale_slice_length` abstains on aliases, rebinding, control-flow changes, and
other growth forms it cannot prove. The project rules require exact resolved
callee contracts and only support direct nested call shapes. Contract indexes,
including a member-call receiver, follow the frontend's call argument order.
See [contracts-v1.md](contracts-v1.md) for the contract schema and examples.

When call-graph reachability is unknown, `specialization_fanout` abstains and
coverage marks reachability incomplete. A selected project group without a
contracts file is incomplete; `--require-complete` returns status 4. Unused
generic bodies are reported separately. A run with partial coverage does not
claim that unsupported patterns are absent. The complete 65-ID disposition is
in [rule-inventory.md](rule-inventory.md).

## Configuration

`--config` accepts strict JSON schema version 1. Supported fields are
`default_groups`, `enable`, `allow`, `deny`, `baseline`, `contracts`, and
`severity`. Unknown fields, duplicate keys, unknown groups, and unavailable
rules fail with status 3.

```json
{
  "schema_version": 1,
  "default_groups": ["existing", "correctness", "suspicious"],
  "enable": ["specialization_fanout"],
  "contracts": ".goose-lint-contracts.json",
  "severity": {"discarded_failure": "error"},
  "deny": [],
  "allow": [],
  "baseline": ".goose-lint-baseline.json"
}
```

Severity values are `error`, `warning`, or `note`; `error` denies a selected
finding. CLI `--group` replaces configured default groups. CLI `--allow`
overrides configured deny and severity; CLI `--deny` has highest rule-selection
precedence. A rule cannot be both allowed and denied by the same config or CLI
invocation.

## Suppressions and baselines

Put a reasoned directive on the finding's statement line or immediately before
it. It binds to one unambiguous statement:

```goose
let count, ok = parse_int(validated_text); // goose-lint: allow[discarded_failure] -- input was validated upstream
```

Suppressed findings remain visible in output with the directive location and
reason. Malformed, unknown, duplicate, and unmatched directives produce
`stale_suppression`. Directive-like text in strings and raw strings is ignored.

Baselines use a versioned fingerprint over rule, normalized path, message,
evidence, specialization context, and duplicate occurrence. They survive line
shifts but not every semantic refactor. Writes require `--write-baseline` and
use an atomic replacement. Baseline matches remain visible; stale entries are
reported individually and can be denied with `--deny stale_baseline`.

## Output and statuses

`--format text` is the default. `--format jsonl` follows
[diagnostics-v1.md](diagnostics-v1.md); the private compiler-to-companion bridge
is specified in [facts-v1.md](facts-v1.md). Output is deterministic for the
same sources, compiler revision, options, config, and baseline.

| Status | Meaning |
|---:|---|
| `0` | Analysis completed without a denied finding. |
| `1` | At least one selected finding was denied. |
| `2` | Source or required import could not be parsed or typechecked. |
| `3` | Invalid CLI option, config, suppression policy, or baseline. |
| `4` | Tool/protocol failure or `--require-complete` found incomplete analysis. |

Only lint mode captures existing compiler warnings as structured findings;
ordinary `goose check` warning text and behavior are preserved.

Measured normal-check and lint-only costs are recorded in
[performance.md](performance.md).
