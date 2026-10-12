# Trust ledger

What the claims in this directory rest on without proof. A theorem is a claim
about the Lean definitions it names and nothing else.

`coverage.json` is a JSON list with one row per feature and claim label, never
merged: `{"feature": string, "label": "specified" | "executable" |
"model-proved" | "instance-checked" | "differential-tested" | "assumed" |
"deferred" | "unsupported", "evidence": string, "limits": string}`; a
`model-proved` row also names the Lean theorem and records the statement
actually proved if it is weaker than the target, and the reviewer's answers.

## Trusted, not proved

| Item | Why it is trusted |
|---|---|
| The compiled Lean oracle (`goose-semantics`) and its runtime | Executable semantics is compiled Lean. Kernel-checked theorems cover the definitions, not the compiler, the interpreter's native code or the C library under it. |
| The Lean kernel and `Lean.collectAxioms` | The audit allows `propext`, `Classical.choice` and `Quot.sound` only; it relies on the axiom collector being complete. `leanchecker` is an optional second kernel pass. |
| The C compiler's determinism | Native-object reuse assumes the same unit text, headers and contract give the same object. |
| The reused runtime entry points: `gs_idxfail`, `gs_divfail`, `gs_divovf`, `gs_ovf`, `gs_abort`, `gs_exit`, and the debug helpers `gs_add_i64` and the other checked-arithmetic and `gs_rangechk` families | The GIR C emitter calls them; their behavior is differential-tested, never modeled or proved. |
| Unbounded storage in the model | The model has no out-of-memory and no stack exhaustion; real exhaustion is outside every safety theorem. |
| The C++ exporter | Its output is `instance-checked` by the Lean validator when present, otherwise `differential-tested`. Nothing proves the exporter translates the source faithfully. |
