# Construction GIR wire forms

This note gives the exact JSON records for construction adapter and published-reference operations in `gir-h/0.4` with the `core-construction` profile. Their verifier and execution contracts are defined in [the construction profile](goose-ir-spec.md#129-construction-in-gir-h04-core-construction).

A record is a JSON array whose first item is its tag. Value IDs are local to a function. Type IDs index the module's ordered type table. Target IDs index the module's ordered target table. An optional origin is encoded as `[]` when absent or `[origin_id]` when present; it is never `null`.

| Record | Exact fields after the tag | Contract |
|---|---|---|
| `i_dest_adapt` | `result_value, source_destination, producer_type_id, request, origin?` | `request` is `"value"` or `"element_run"`. The source is an open receiving destination. The producer and receiver must be nonfixed array types with the same element type, and the producer must adapt to the receiver. The result is `dest producer_type request`, while retaining the original receiving channel and its metadata. The channel must be empty and not already adapted. |
| `i_dest_adapt_finish` | `result_value, closed_carrier, origin?` | Consume a completed or cancelled adapted carrier and restore its original receiving type and request. The result preserves whether the producer completed or was cancelled. It retains the original destination start while restoring receiver metadata after any required in-place normalization. |
| `i_dest_publish_ref` | `result_value, built_carrier, origin?` | Consume a completed `value` carrier from exactly one `dr_push` channel, publish that element, and return `ref mut element` to its published location. Other receivers, `element_run` requests, and channels without exact push provenance are invalid. |

The target records used by construction exits are:

| Record | Exact fields after the tag | Contract |
|---|---|---|
| `target` | `[member_function_ids]` | Nonempty, sorted, duplicate-free function IDs. Target members have the same sequence of result types and requests. |
| `i_target_dest` | `result_value, target_id, result_position, origin?` | Open the replacement destination for that result position in the selected active target activation. |
| `t_invoke` | `callee, [arguments], [result_destinations], normal_block, [normal_forwarded_values], [escape_edges], origin?` | Call with a normal continuation and target-specific escape continuations. |
| `escape_edge` | `target_id, block_id, [block_arguments]` | Select the continuation for one target ID. |
| `t_escape` | `target_id, [result_carriers], [cancelled_channels], origin?` | Transfer results to the selected target and cancel the current activation's superseded result channels. |

The decoder rejects malformed arity, out-of-range table IDs, empty target records, and unsorted or repeated target members before verification. Well-shaped records with invalid channel ownership, adaptation lineage, request, or active-target membership fail GIR verification.
