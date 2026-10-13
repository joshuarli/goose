# Trust ledger

What the claims in this directory rest on without proof. A theorem is a claim
about the Lean definitions it names and nothing else.

The core soundness store invariant requires every stored global value to be
non-reference storage, even at roots outside the initialized declarations.
It permits values of concrete flat fixed types at undeclared roots; resizable
and limited owners require declared global storage. This prevents untracked
global slice holders and owner roots from bypassing initialization and shrink
authority.
Content-root annotations may include harmless extra roots. The core soundness
frame therefore tracks owner authority separately from content typing: only
parameters declared as references to grow or growshrink storage grant owner
authority, and stored references of those types retain that authority. Slice
contents and returned slice values continue to use the broader content roots.

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
| The C compiler's determinism | Native-object reuse assumes fixed unit text, recorded headers and build contract produce the same object. Verification mode re-compiles reused objects, but one successful comparison does not prove determinism. |
| Completeness of native-object inputs | The key uses the unit text, the compiler's reported non-system header dependencies where available, and the compiler/build contract. A compiler without dependency-file support falls back to the runtime header and explicitly named headers. The tests exercise this path; they do not prove that every transitive input is covered. |
| Completeness of whole-build inputs | The no-op build key uses the files read and paths probed by the recording reader, plus the build contract. The reuse tests exercise this recorder; they do not prove that every effect of every external tool or resource is recorded. |
| Completeness of checked-result dependencies | `cachedRun_eq` assumes the key determines the result (`KeyDetermines`); `wrong_answer_without_key_determination` shows the assumption cannot be dropped. Real checked-result reuse is deferred. The dependency sets are recorded and shadow-tested against recomputed results, but no checked result is reused from them. |
| Sharing of emitted implementations | The Lean sharing theorem is about Lean module quotients under its explicit hypotheses. The production `--share` pass merges equal emitted C bodies and compatible callee classes after each context has been checked; tests qualify representative cases but neither the theorem nor the tests prove the C++ pass preserves semantics for every possible program. |
| Units emission and native linking | The proofs do not cover the production unit partitioner, its C text, native compiler invocations, object store, or linker. Corpus and locality checks provide finite differential evidence only. |
| The reused runtime entry points: `gs_idxfail`, `gs_divfail`, `gs_divovf`, `gs_ovf`, `gs_abort`, `gs_exit`, and the debug helpers `gs_add_i64` and the other checked-arithmetic and `gs_rangechk` families | The GIR C emitter calls them; their behavior is differential-tested, never modeled or proved. |
| Unbounded storage in the model | The model has no out-of-memory. Call nesting deeper than 100000 is a timeout at every fuel, not a stack exhaustion, so a deeply recursive terminating program has no `done` result in the model; real exhaustion of memory or stack is outside every safety theorem. |
| The C++ exporter | Its output is `instance-checked` by the Lean validator when present, otherwise `differential-tested`. Nothing proves the exporter translates the source faithfully. |
