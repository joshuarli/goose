# GIR bounds certificate qualification

The proof gate is complete. `Goose.Proofs.Bounds.reachable_facts` derives runtime certificate facts from accepted GIR validation and actual reachability. `Goose.Proofs.Bounds.checked_run` preserves the whole run when every proven index becomes a checked index. The theorem accepts every numeric profile and fuel value. Its axiom audit reports `propext`, `Classical.choice`, and `Quot.sound`.

The production gate requires the compiler to emit proven indexes on pilot sources. The focused command is:

```sh
sh test/gir/bce/check.sh path/to/debug/goose path/to/goose-semantics
```

The runner checks these sources:

| Source | Required indexes | Expected outcome at fuel 256 |
|---|---|---|
| `returned.goose` | At least one proven index | Return after printing `7` |
| `aborted.goose` | At least one proven index | User abort after printing `true` |
| `called.goose` | At least one proven index | Return after printing `true`, `7`, and `9` |
| `looping.goose` | At least one proven index | Timeout after printing `true` |
| `call_kill.goose` | Checked indexes | Return after printing `true` |
| `scope_kill.goose` | Checked indexes | Return after printing `11` |
| `loop_counter.goose` | Checked indexes | Return after printing `11` |

Each source must export `gir-h/0.4` under `core-pilot`. Lean independently decodes, validates, and re-encodes each emitted module. The runner replaces every `i_index_proven` with `i_index` carrying no origin, matching `checkedOp`. It validates the original module. It runs the replacement with `--no-validate`, matching the theorem's interpreter target. The runner compares the full outcome, abort origin, output, and exit status at fuels 0, 1, 8, 32, and 256 under release and debug arithmetic.

The runner also requires `GIR-V080` rejection for missing certificates, facts absent from a predecessor, a call that kills length facts, and a scope transition that kills length facts.

At compiler source `ee5eaa8d`, all seven sources export and independently validate. The four positive sources emit proven indexes, and the three kill controls emit only checked indexes. Their outcomes match the table under both numeric profiles at fuels 0, 1, 8, 32, and 256. The run also rejects all four forged modules with `GIR-V080`.

Direct `Len` reads from fixed arrays and `Grow`, `GrowShrink`, or `Limited` owners lower to `i_alen`. `VarArr` keeps snapshot-based length handling. Before evidence proposal, `NormalizeGirEvidenceInputs` rewrites repeated `Slot` or `Global` owner operands only when every reachable incoming path carries the same dominating address SSA value. It clears slot aliases at scope entry and exit when a slot belongs to that scope or a nested scope. It also rewrites an index operand to an equal nonnegative I64 constant already named by a live comparison fact. These operand rewrites let the compiler use the existing exact-SSA evidence rules. The C++ verifier and Lean checker remain unchanged.
