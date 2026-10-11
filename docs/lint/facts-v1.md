# Private lint facts stream v1

`goose lint` parses, resolves, and typechecks with the production C++ frontend.
Before optimization or code generation, `BuildLintFacts` writes the private
facts consumed by the adjacent Goose companion. The companion validates the
entire stream and all references before evaluating rules. Neither source text
nor raw AST pointers are serialized. The compiler removes the owner-only
temporary files after the companion exits.

## Framing and ordering

The stream is UTF-8 JSON Lines: one JSON object followed by LF per record, with
a final LF. Fields are closed shapes; unknown or duplicate keys, invalid
references, out-of-order records, malformed JSON, and trailing bytes fail
closed.

Record phases are fixed:

1. One `header`.
2. `source` records sorted by normalized path, with dense IDs.
3. `warning` records sorted by path, source start, code, and message. Each
   carries sorted unique checked-specialization contexts.
4. `statement` records sorted by file ID, start, end, and source order.
5. `comment` records sorted by file ID and source span, with dense IDs.
6. `specialization` records sorted by path, declaration line, function
   identity, and concrete context, with dense IDs.
7. `call` records sorted by specialization ID, path, start, and use shape,
   with dense IDs. Calls in globals have a null specialization ID.
8. `result_use` records sorted by call ID and result index.
9. `call_argument` records sorted by call ID and argument index.
10. `pure_value` records sorted by file, source span, and specialization.
11. `overflow_guard` records with dense IDs.
12. `slice_length` records with dense IDs.
13. `coverage` records in source-file order.
14. One terminal `end` record.

The `end.record_count` counts all prior records and excludes itself. Its
`integrity` is FNV-1a 64 over the exact bytes of each preceding record,
including each LF, as `fnv1a64:<16 lowercase hex digits>`. This detects
accidental corruption; it is not a cryptographic authenticity check.

The producer and reader cap one record at 16 MiB, the stream at 512 MiB, and the
record count at eight million. Exceeding a limit is a tool failure, never a
truncated success. Source-content hashes use the same FNV-1a 64 encoding over
the exact source bytes.

## Record schemas

The snippets show each closed shape. Nullable values are JSON `null`, not
omitted.

```json
{"kind":"header","facts_version":1,"compiler":"goose","compiler_revision":"<runtime-id>","entries":["src/app.goose"],"profile":"O1","frontend_options":{"debug":false,"unsafe_no_rf_check":false,"allow_fetch":false}}
{"kind":"source","file_id":0,"path":"src/app.goose","content_hash":"fnv1a64:<16 hex>","byte_length":1200,"line_endings":"lf"}
{"kind":"warning","id":0,"code":"redundant_cast","message":"existing compiler text","source":{"file_id":0,"line":12,"start_line":12,"start_column":8,"end_line":12,"end_column":19,"start_byte":80,"end_byte":91,"precision":"exact"},"specializations":["app::run (args() roots() views() bindings() escaped=false funval=false)"]}
{"kind":"statement","file_id":0,"path":"src/app.goose","start_byte":80,"end_byte":100,"start_line":12,"end_line":13,"source_order":7}
{"kind":"comment","id":0,"file_id":0,"path":"src/app.goose","start_byte":101,"end_byte":133,"line":14,"form":"line","text":"// goose-lint: allow[rule_id] -- reason"}
{"kind":"specialization","id":0,"file_id":0,"path":"src/app.goose","start_byte":50,"end_byte":100,"start_line":4,"end_line":6,"start_column":1,"end_column":2,"precision":"exact","name":"app::run","context":"args() roots() views() bindings() escaped=false funval=false","entry_reachable":true}
{"kind":"call","id":0,"specialization_id":0,"file_id":0,"path":"src/app.goose","start_byte":150,"end_byte":170,"start_line":20,"end_line":20,"start_column":12,"end_column":32,"precision":"exact","callee_id":"stdlib::parse_int","builtin_id":null,"result_arity":2,"arg_count":1,"use_shape":"tuple_binding"}
{"kind":"result_use","call_id":0,"result_index":1,"state":"bound","binding_name":"ok","referenced":false}
{"kind":"call_argument","call_id":0,"index":0,"shape":"identifier","variable_id":"v0:140:0","nested_call_id":null}
{"kind":"pure_value","id":0,"specialization_id":0,"file_id":0,"path":"src/app.goose","start_byte":200,"end_byte":203,"start_line":25,"end_line":25,"expression_kind":"constant_integer_expression","proof":"typed-subtree-effect-free-and-nontrapping"}
{"kind":"overflow_guard","id":0,"specialization_id":0,"file_id":0,"path":"src/app.goose","operation":"add","signed":true,"width":32,"right_nonnegative":true,"result_matches":true,"source_matches":true,"relation":"lt","result_name":"sum","source_name":"left","arithmetic_start_byte":80,"arithmetic_end_byte":90,"arithmetic_start_line":8,"arithmetic_end_line":8,"arithmetic_start_column":15,"arithmetic_end_column":25,"guard_start_byte":100,"guard_end_byte":120,"guard_start_line":9,"guard_end_line":9,"guard_start_column":5,"guard_end_column":25}
{"kind":"slice_length","id":0,"specialization_id":0,"file_id":0,"path":"src/app.goose","view_name":"view","root_name":"items","capture_before_growth":true,"growth_before_use":true,"same_root":true,"index_uses_current_length":true,"capture_start_byte":130,"capture_end_byte":140,"capture_start_line":10,"capture_start_column":15,"capture_end_column":25,"growth_start_byte":145,"growth_end_byte":160,"growth_start_line":11,"growth_start_column":5,"growth_end_column":20,"use_start_byte":165,"use_end_byte":185,"use_start_line":12,"use_end_line":12,"use_start_column":5,"use_end_column":25}
{"kind":"coverage","file_id":0,"path":"src/app.goose","parse":"complete","semantic":"entry-reachable-specializations","checked_specializations":2,"unchecked_generics":1,"unsupported":[]}
{"kind":"end","record_count":13,"integrity":"fnv1a64:<16 lowercase hex>"}
```

### Header, sources, and warnings

`header.facts_version` is 1. It includes compiler identity, runtime revision,
one entry path, the selected profile (`O0`, `O1`, or `O2`), and frontend
options that affect the run. The revision is Goose's runtime version, not a
source-control SHA.

`source.path` uses project-relative forward slashes where possible. Standard
library and package sources receive `stdlib/` and `packages/<name>/` prefixes.
Paths outside the project are mapped to `external/<hash>/<basename>` so host
directories are not exposed. IDs index the path-sorted source table.
`line_endings` is `lf`, `crlf`, `cr`, `mixed`, or `none`.

`warning` carries existing compiler warning text and stable site-assigned
codes: `redundant_cast`, `redundant_reference_marker`, and
`avoidable_reference_copy`. `specializations` is a sorted, unique array of
typed specialization context strings that emitted the same warning after the
typechecker's normal deduplication. It can be empty for a warning without a
function specialization. The nested `source.file_id` can be null for an
unmapped source. Exact spans use 0-based, half-open byte offsets and 1-based
byte columns. For line precision, offsets and columns are null. Codes are never
inferred from message text.

### Source spans and suppressions

`statement` contains the original source span used to bind a local suppression
to one statement. It does not serialize an AST statement kind. `comment`
contains only lexer-recognized comments whose text contains
`goose-lint:`; string and raw-string contents do not create comment facts.
Spans use 0-based, half-open byte offsets.

### Specializations and calls

`specialization` describes a checked function context in stable textual form.
Each present root class in the context includes its normalized `depthkey`;
the text places `:depthkey<N>` after the positive class index and before its
other context flags. Classes without a root have no depth key. The key preserves
how a root class's depth relates to the lexical environment, including the
distinction between a global root and a local root beyond that environment. Its
declaration location is exact when available; otherwise offsets and columns
are null and `precision` is `line`. `entry_reachable` is true or false when the
selected call graph is complete and null when reachability is unknown. IDs are
stream-local.

`call` records the resolved package-qualified callee when available, exact
builtin identity, result arity, source span, and syntactic consumption shape:
`statement`, `tuple_binding`, `scalar`, `return`, or `unknown`.
Argument count includes a member-call receiver as argument zero. Calls in
globals have a null specialization ID.

`result_use` state is `discarded`, `bound`, `overwritten`, `returned`, or
`unknown`. A bound status is referenced only if it is read. The producer
distinguishes a local status overwritten in straight-line code before any
inspection. `binding_name` and `referenced` are null when the result has no
local binding. A scalar use of a multi-result call marks later results
discarded. Unknown relationships remain unknown.

`call_argument.shape` is `identifier`, `slice`, `call`, or `other`.
An identifier carries a stream-local `variable_id`; a full slice carries the
identity of its root variable; a nested call carries a `nested_call_id`.
Fields not used by that shape are null. These facts support exact contract
matching; the contract file supplies application meaning.

### Rule facts

`pure_value` is emitted only for a standalone statement whose complete typed
subtree is proved to have no observable effect and not to trap. Kinds include
integer, floating, boolean, and string literals, plus constant nontrapping
integer expressions. Calls, mutation, I/O, aborts, unknown operations, and
possibly trapping arithmetic are excluded.

`overflow_guard` records only adjacent typed signed integer add/subtract and
result/source comparison shapes. Its booleans identify a typed nonnegative
right operand and exact variable matches; the Goose engine decides whether the
operation/relation is the canonical post-operation check. Both arithmetic and
guard spans include byte offsets, lines, and byte columns.

`slice_length` records only a same-block full-slice capture, a direct
same-root positive growth operation, and a later view index using the root's
current `len - 1`. Ordering, owner identity, and shape booleans are explicit.
Every capture, growth, and use span includes byte offsets, lines, and columns.
Other control flow and aliases are outside this proof and are skipped.

### Coverage and failures

`coverage.semantic` is `entry-reachable-specializations`. Counts are per
source. The record reports checked entry-reachable specializations, unchecked
generic bodies, and unsupported analyses. Every specialization also carries
its reachability state. When dynamic reachability is unknown, coverage includes
`specialization_reachability` and `specialization_fanout`; fanout is then
inconclusive. Missing unsupported-list entries do not imply support unless a
rule is explicitly listed as implemented in
[`rule-inventory.md`](rule-inventory.md).

There is no private `error` record. Parse/typecheck errors use the public JSONL
error envelope. Facts or companion failures use tool-error status 4 rather than
returning zero findings.
