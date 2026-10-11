# Project API contracts v1

Project rules use a strict JSON file selected by the `contracts` field in lint
config. The file assigns exact resolved function identities to narrow API
roles. Names are never guessed from a callee spelling. Unknown or duplicate
keys, malformed roles, conflicting role assignments, and out-of-range argument
indexes are errors.

```json
{
  "schema_version": 1,
  "apis": [
    {"callee": "app::append_value", "role": "append_to", "owner_arg": 0},
    {"callee": "app::find_index", "role": "index_of", "owner_arg": 0},
    {"callee": "app::use_index", "role": "consumes_index", "owner_arg": 0, "index_arg": 1},
    {"callee": "app::consume_after_growth", "role": "view_after_append", "view_arg": 0, "append_arg": 1}
  ]
}
```

`callee` uses the compiler's resolved `package::function` identity. Argument
indexes are zero-based in the frontend's normalized call list; member-call
receivers occupy index zero. Each role accepts exactly the fields shown below.

| Role | Required indexes | Meaning used by the linter |
|---|---|---|
| `append_to` | `owner_arg` | The API grows the referenced owner. |
| `index_of` | `owner_arg` | The API produces an index for the referenced owner. |
| `consumes_index` | `owner_arg`, `index_arg` | The API uses the index against the specified owner. |
| `view_after_append` | `view_arg`, `append_arg` | The callee uses the view after evaluating the append argument. |

`view_before_append_argument` requires a direct full-slice argument before a
later nested call whose exact identity has an `append_to` role. The nested
call's direct owner must be the same local variable as the slice root, and
both calls must be in the same checked function specialization. This is enough
to prove left-to-right argument evaluation creates the view before growth and
the outer API consumes the view afterward.

`foreign_container_index` requires a direct nested call in `index_arg` whose
identity has an `index_of` role. The producer and consumer owners must be
direct local identifiers and differ. Both calls must belong to the same source
and checked specialization. A raw integer, alias, wrapper call, or uncertain
owner does not trigger the rule.

Contracts describe application semantics; the linter validates their syntax
and callee arity at use sites but cannot prove that a declared API role matches
the function body. Review contract changes with the project code they describe.
