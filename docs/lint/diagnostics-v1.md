# Public lint JSONL v1

`goose lint --format jsonl` writes a deterministic stream to stdout. Every
record is one UTF-8 JSON object followed by LF. Source locations use normalized
project-relative paths, 0-based half-open UTF-8 byte offsets, and optional
1-based byte columns. JSON strings escape quotes, backslashes, and control
bytes. The compiler does not print startup or typecheck logs into this stream.

The v1 success stream contains a `header`, zero or more `diagnostic` records,
per-source `coverage` records, optional `baseline` records, optional `error`
records for mandatory incomplete analysis, and one final `summary`. Diagnostics
are sorted by path, source line/byte, rule code, evidence, and specialization
context. Cosmetic wording may change; schema keys and rule semantics are the
compatibility boundary.

Diagnostic `severity` is `error`, `warning`, or `note`. The default is
`warning`; a config severity of `error` denies the selected finding, while
`warning` and `note` do not. The rule's group and confidence (`high` or
`medium`) are separate from severity. CLI `--allow` overrides configured
severity for denial; CLI `--deny` forces denial.

## Successful result

```json
{"kind":"header","schema_version":1,"tool":"goose-lint","compiler_revision":"<runtime-id>","entries":["src/app.goose"],"profile":"O1"}
{"kind":"diagnostic","schema_version":1,"code":"discarded_failure","group":"correctness","severity":"warning","confidence":"high","message":"stdlib::parse_int status result is discarded","primary":{"path":"src/app.goose","start_byte":120,"end_byte":141,"start_line":8,"start_column":9,"end_line":8,"end_column":30,"precision":"exact"},"related":[],"evidence":{"callee":"stdlib::parse_int","status_result":1,"use":"discarded"},"specializations":["app::run (args() roots() views() bindings() funval=false)"],"suppression":null,"baseline":null,"suggestion":null,"fixable":false}
{"kind":"coverage","schema_version":1,"path":"src/app.goose","parse":"complete","check":"partial","checked_specializations":2,"unchecked_generic_bodies":1,"unsupported":[{"analysis":"post_overflow_guard","reason":"required semantic facts are not available"}]}
{"kind":"summary","schema_version":1,"findings":1,"suppressed":0,"baselined":0,"stale_baseline_entries":0,"errors":0,"exit_status":0}
```

`header` has the compiler runtime identifier, selected root entry paths, and
profile. The identifier is not a source-control revision. `diagnostic` records
have stable rule `code`, group, severity, confidence, human message, a primary
location, related locations, evidence, applicable specialization contexts,
optional suppression/baseline metadata, and optional fix suggestion. `related`
is currently empty; `suggestion` is currently null and `fixable` is false.

An exact primary location has integer byte offsets and line/byte-column values.
A line-only location has null offsets and columns; it never fabricates token
precision. `evidence` is either JSON null or a rule-specific JSON object.
Suppressed findings remain in the stream and include a `suppression` object with
the reason and comment location. Baseline matches remain in the stream and
include a `baseline` object with their fingerprint and local occurrence number.
Findings can therefore be distinguished from findings suppressed locally or
accepted through a baseline.

Coverage is explicit for each parsed source. `parse` is `complete` after the
frontend succeeds. `check` currently reports `partial` when required analyses
are unavailable or generic bodies are unchecked. Counts describe checked
entry-reachable specializations and unchecked generic bodies. Each unsupported
item has an analysis ID and reason. A clean output with partial coverage is not
a claim that unsupported patterns are absent.

With `--write-baseline`, a `baseline` record reports the number of findings
written. Baseline entries are sorted by fingerprint and contain
`fingerprint`, `code`, `path`, `occurrence`, `message`, and canonical context.
The fingerprint algorithm is FNV-1a 64 with versioned field framing over rule,
normalized path, message, evidence, specialization context, and a local
occurrence number. It is designed to survive line shifts, not arbitrary
semantic refactors. Specialization context strings include the normalized
depth key for each present root class so otherwise identical displayed
contexts can distinguish semantically distinct root-depth relationships.
Adding this context detail changes fingerprints for affected findings; an
existing baseline may need regeneration. Baseline output is written atomically
only when explicitly requested.

When existing baseline entries do not match current findings, each stale entry
is reported as a `baseline` record with `status:"stale"`, fingerprint, code,
and path. Stale entries do not hide new findings. They do not fail a run unless
`stale_baseline` is selected for denial, for example with
`--deny stale_baseline`.

## Error records and process statuses

CLI and policy errors use this envelope in JSONL mode:

```json
{"kind":"header","schema_version":1,"tool":"goose-lint","compiler_revision":"<runtime-id>","entries":["src/app.goose"],"profile":"O1"}
{"kind":"coverage","schema_version":1,"path":null,"parse":"not_run","check":"not_run","checked_specializations":null,"unchecked_generic_bodies":null,"unsupported":[]}
{"kind":"error","schema_version":1,"code":"invalid_config","message":"configuration is invalid","exit_status":3}
{"kind":"summary","schema_version":1,"findings":0,"suppressed":0,"errors":1,"exit_status":3}
```

Source/import errors include stage-aware `parse` and `check` coverage. The
compiler and companion both use the same error codes: `invalid_config`,
`missing_import`, `invalid_source`, `analysis_incomplete`, and `tool_failure`.
Human-readable messages may change and must not be used as machine IDs.

| Status | Meaning |
|---:|---|
| `0` | Analysis completed; no selected, unsuppressed finding was denied. |
| `1` | Analysis completed with one or more denied findings. |
| `2` | Source or required import could not be parsed/typechecked. |
| `3` | Invalid lint option, config, suppression policy, or baseline. |
| `4` | Tool/protocol failure or `--require-complete` found unsupported analysis. |

Compiler errors cannot be hidden by `--allow`. Text-mode compiler failures are
written to stderr; JSONL-mode errors go to stdout as valid records. A missing
companion or corrupt facts stream never becomes empty success.

The compiler caps private facts at 512 MiB; the Goose companion caps its output
at 256 MiB. The parent reads only the owner-only output path created for that
invocation. Facts and result temporary files are removed on normal return and
failure.

Specialization contexts omit the obsolete escaped-scope distinction.
Baselines containing the previous context strings require explicit refresh.
