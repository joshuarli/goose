# Goose IR construction native contract

This note records the construction-only wire operands and their lowering into the C backend. The complete semantic contract remains in [Goose IR specification §12.9](goose-ir-spec.md#129-construction-in-gir-h04-core-construction) and [§12.10](goose-ir-spec.md#1210-construction-low-gir-l02). Pilot and shrink records keep their existing encodings.

## High GIR destination records

All records below are selected only by `core-construction`. `val` operands name SSA values; `ty` is a type-table index; `org?` is the existing optional origin encoding.

| Record | Exact fields after the tag | Result and effect |
|---|---|---|
| `i_dest_publish_ref` | `val result, val built, org?` | Consumes a completed push destination, publishes its new element, and returns `ref mut E` to that element. |
| `i_dest_adapt` | `val result, val receiving_dest, ty producer_type, Request producer_request, org?` | Produces an adapted destination for a producer whose array-family representation or request differs from the receiver. It retains the original receiver metadata and storage. |
| `i_dest_adapt_finish` | `val result, val built_or_cancelled, org?` | Restores the saved receiving carrier type and request while preserving whether the producer completed or was cancelled. When the producer added an outer prefix absent from the receiver, lowering removes it in place and updates the stack top. |
| `x_dest_snapshot` | `val dest, val fixed_snapshot, org?` | Writes the already evaluated fixed-array elements in order. It emits element writes, not an ordinary storage-copy event. |
| `x_dest_repeat` | `val dest, val completed_source, org?` | Copies one completed fill value into each destination element, then consumes its private source. A construction trace records each copy with reason `repeat`. |
| `x_dest_copy` | `val dest, val source_ref_or_sampled_view, org?` | Samples and copies completed source storage once. A trace retains the source descriptor's storage and path. |
| `x_dest_publish` | `val built, org?` | Publishes a completed destination exactly once and updates its receiver's visible length or metadata. |

For a direct `CoreView::Of` length read, the high exporter evaluates the place once and emits `i_alen` on its reference when the pointee is `arr`, `grow`, `growshrink`, or `limited`. `varr` and other view expressions retain the `i_snap`/`i_vlen` path. This leaves the owner address available to the existing bounds-evidence matcher without changing sampled-view semantics.

## Low result descriptors

For `core-construction`, `gir-l/0.2` extends `lfunc` with one mandatory descriptor list between scopes and blocks:

```text
lfunc name [parameter_types] [] stack_count [members] [scope_parents] [lresult...] [blocks]
lresult_scalar source_type_key primitive_type output_parameter
lresult_snapshot source_type_key byte_extent output_parameter
lresult_reference source_type_key address_output_parameter
lresult_resizable_reference source_type_key header_output_parameter stack_output_parameter
lresult_slice source_type_key data_output_parameter count_output_parameter
lresult_nonfixed source_type_key request stack_parameter start_parameter count_parameter
```

Descriptor position is source result position. Output parameter positions form one ordered, distinct, consecutive suffix of the primitive function signature. Every named parameter is a pointer. Scalar descriptors name an integer or boolean primitive; snapshot extents are positive; reference outputs contain native pointers; slice counts and nonfixed counts are signed 64-bit integers. A nonfixed request is exactly `value` or `element_run`. Functions and global initializers with no results carry `[]`; omission is rejected. Pilot and shrink retain their previous seven-field `lfunc` records byte for byte. This profile-specific extension stays under `gir-l/0.2`; it does not add a fallback for the old construction record.

A source type key is an opaque nonnegative module-local identity. Equal keys require equal physical descriptor kinds and layouts, independently of parameter positions and nonfixed request. Every member of one target must agree on result keys, descriptor kinds, layouts, and requests. The key preserves nominal distinctions within a checked low module; it does not prove that lowering faithfully translated the original source type. That is a separate translation obligation.

The primitive parameter layout and C ABI are unchanged. The nonfixed count pointer still addresses two signed 64-bit fields: count at offset zero and destination identity at offset eight. The caller initializes both fields before invocation. The callee may read this incoming construction state, but must write its final count on normal return. Nonzero return discriminants do not initialize normal result outputs.

The verifier follows output addresses through frame addresses, constant offsets, block parameters, local members, and currently installed target cells. It checks each function's normal output writes and each call's output separation and incoming metadata. Call outputs become readable only on the corresponding zero-discriminant edge or after an actual covering write. A merge retains initialization only when every incoming path proves it. Unknown aliases do not prove initialization. While a call awaits dispatch of its return discriminant, only pure scalar/address computations and control flow may execute; effects and memory reads require the corresponding normal or target edge. Different pending calls cannot merge. Ordinary calls cannot resume while an escaped result is in flight; forwarding and receiving epilogues use the closed cleanup operations.

A member catch must transfer each exact escaped scalar, pointer, or count to its matching output channel. Loading or comparing a payload is insufficient. Complete snapshot copies retain byte provenance through aggregate frame staging. Later overlapping writes, including header writes, invalidate that transfer. Forwarding frames must retain the in-flight target discriminant and payload cells. Saved outer recursive cells and values retained across another call cannot stand in for the current payload. Reference source descriptors must follow their matching result channel. A forwarding `l_mark` retains the escaped end identity only while the tracked stack top is unchanged.

Nonfixed handlers save each escaped end pointer in a frame scalar member. Before moving a landed interval, code compares `escaped_start + computed_byte_count` with that saved end. Only the true edge proves that the exact interval is moved; the false edge triggers the existing assertion abort before copying. The native count record remains 16 bytes. Each such result adds one pointer-sized frame member and one endpoint comparison and branch per landing. The verifier also requires the escaped count to reach the receiving count output. These checks establish declared output initialization and exact payload transfer; they are not a general proof of arbitrary low pointer memory safety.

## Low target table and operations

The construction suffix of `gir-l/0.2` is a list of target tables:

```text
ltarget [member_function_ids] [cell_type_ids] [lchannel...]
lchannel result_position [incoming_cell_indices] [escaped_cell_indices]
```

`result_position` is the zero-based source result position. Channels appear in result order, so position `n` must equal channel index `n`; the verifier rejects negative, duplicate, missing, or reordered positions. Cell 0 is the boolean `active` flag. For each result in order, the table then allocates that result's incoming cells followed by its escaped cells. Every cell belongs to exactly one channel side.

For a fixed result, incoming cells are the addresses of its ordinary output words; escaped cells hold the corresponding primitive result words, or one pointer to the completed aggregate snapshot. For a nonfixed result, incoming cells are three pointers `(stack, saved_start, count_output)` and escaped cells are `(value_start, value_end, i64_count)`. These are cell indices, not byte offsets. The C emitter declares one typed thread-local C cell for each entry.

| Low record | Exact fields after the tag | Native effect |
|---|---|---|
| `l_rf_get` | `val result` | Reads the current thread's return discriminant. |
| `l_rf_set` | `val discriminant` | Stores zero for normal return or `target_id + 1` for a target return. |
| `l_target_load` | `val result, target_id, cell_index` | Loads the typed thread-local target cell. |
| `l_target_store` | `target_id, cell_index, val` | Stores the typed cell. Entry code saves prior cells, sets `active`, then installs incoming output pointers; exit code restores the saved cells. |
| `l_source_target_enter` | `val token, target_id, [optional_primitive_output_position]` | In trace mode, pushes the activation's result-source mapping. An empty position marks a non-reference result channel. |
| `l_source_target_result` | `target_id, result_position, val_source` | In trace mode, attaches a source descriptor to a returned reference channel. |
| `l_source_target_get` | `val result, val token, result_position` | In trace mode, reads the source descriptor captured for that activation. |
| `l_source_target_leave` | `val token` | In trace mode, pops that activation's provenance frame. |

An escaping low call remains an ordinary `i_call`. It reads the return flag immediately afterward, branches on zero for normal output, and compares each statically possible `target_id + 1` before entering that target's handler. The verifier checks activation ownership, installed and restored cells, discriminant coverage, handler operations, and the unreachable invalid-tag sentinel before native emission.

## Native stack and provenance handling

Construction calls use a dynamic stack directory. `l_stack_at` resolves `(base, offset)` to a lazily created stable `gs_stack` cell, so recursive frames do not share the same stack object. Since recursive depth has no static bound, construction initializes the runtime's region-count cap to `GS_STACK_BUDGET / (GS_STACK_RESERVE + GS_STACK_GAP)`. Pilot and shrink continue to pass their statically counted region totals.

When no construction trace is requested, source-provenance operations have no native effect and trace IDs use zero. Trace-enabled emission retains descriptors across calls and target activations, recording storage identities and element paths without treating metadata pointers as program addresses. Destination events do not alter stdout or data layout.

## Focused checks

The `compiler_gir` checks cover mandatory result descriptors, typed output positions and type identities, channel-position serialization, missing or duplicate activation, incomplete or repeated target dispatch, dummy payload uses, constant and overwritten landing values, shortened moves, incorrect endpoints, and reads of normal output cells on an escape edge. The recursive multi-result fixture in `test/semantics/sem_construction_source_exit_recursive_multi.goose` checks two fixed result channels through an inner target return and recursive caller restoration.
