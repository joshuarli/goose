# Lean 4.35 paranoid semantic audit

The semantic dependency audit passes at source `27feef55` under Lean 4.35.0.
All five independent kernels accept fresh official exports of the 171 registered theorems and the logical dependencies of `Main.main`.
This qualifies the named semantics, not every declaration in the Lean distribution.
The external managed default remains unchanged.

## Scope and result

`test/semantics/paranoid_roots.lean` derives theorem roots from `Goose.Audit.registry` and adds `main` from the `Main` module.
It follows every type and body, including opaque bodies, mutual inductive declarations, constructors, and recursor rules.
Missing source declarations fail the audit.
Proof dependencies must use only `propext`, `Classical.choice`, and `Quot.sound`.
Unsafe or partial proof dependencies fail the audit.

The 171 theorem roots have 34,593 dependency constants.
`Main.main` has 16,502 dependency constants.
Their union has 42,440 constants, all safe.
The official exports contain 42,935 distinct constants because the exporter also includes induced recursor packages.
Streaming name decoding verifies that the exports contain every root and all 42,440 dependencies.
The decoder preserves name components containing dots and quoted syntax names.

Both exports pass Lean paranoid, lean4lean, nanoda, con-leche, and con-ron:

| Export | Bytes | Largest checker RSS |
|---|---:|---:|
| 171 registered theorem roots | 1,056,637,573 | 3,967,102,976 |
| `Main.main` | 79,203,464 | 572,989,440 |

The replay uses the bundled checkers and their standard axiom allowlist.
Nanoda uses one thread, with a 256 MiB Rust worker stack and a 256 MiB process stack limit.
Guards enforce the 8 GiB checker budget and retain at least 16 GiB of host memory.
No source definition or checker implementation was replaced.
The exports and complete checker output are retained in `.work/wt/close-paranoid/.work/tmp/` as `relevant-claims.*` and `relevant-runtime.*`.
`relevant-export-coverage.log` records the exact parsed union.

The `main` closure concerns logical Lean declarations.
Native initialization, extern implementations, `implemented_by` replacements, code generation, and the compiled executable retain their separate trust and verification obligations.
New theorem registrations or changed dependencies require fresh exports and replay.

## Reproduce the root selection

Run these commands from the repository root with source-qualified build artifacts in `semantics/.lake/build/lib/lean`.
Select the explicit Lean 4.35 installation without changing the managed default.

```sh
export PATH="$HOME/.local/lib/lean4/v4.35.0/bin:$PATH"
unset LEAN_SYSROOT ELAN_TOOLCHAIN LEAN_TOOLCHAIN
export LEAN_PATH="$PWD/semantics/.lake/build/lib/lean"
export TMPDIR="$PWD/.work/tmp"
mkdir -p "$TMPDIR"
lean --run test/semantics/paranoid_roots.lean roots > "$TMPDIR/paranoid-roots.tsv"
mapfile -t proof_roots < <(jaq --from tsv -r 'select(.[1] != "main") | .[1]' "$TMPDIR/paranoid-roots.tsv")
leanexport Main -- "${proof_roots[@]}" > "$TMPDIR/paranoid-claims.ndjson"
leanexport Main -- main > "$TMPDIR/paranoid-main.ndjson"
lean --run test/semantics/paranoid_roots.lean verify "$TMPDIR/paranoid-claims.ndjson" "$TMPDIR/paranoid-main.ndjson"
```

`closure` prints the complete dependency selection with separate theorem and `main` membership.
`verify` checks declaration coverage, not kernel acceptance.
Replay each export with `leanchecker-paranoid --silent --from-export`, `lean4lean --import`, `nanoda_bin`, `con-leche`, and `con-ron`.
Nanoda takes the standard Lake JSON configuration, with the export path and `num_threads` set to one.
Run each checker under the memory guards above.

The focused controls check valid proofs, opaque bodies, recursors, forbidden axioms, `sorry`, missing source dependencies, missing exports, and malformed name references:

```sh
lean -o "$TMPDIR/paranoid_roots.olean" test/semantics/paranoid_roots.lean
LEAN_PATH="$TMPDIR:$LEAN_PATH" lean test/semantics/paranoid_roots_checks.lean
```

## Replaced imported-environment census

The earlier 161,796-name selection enumerated all noninternal constants in imported environments.
That included unused Lean parser, elaborator, runtime, and standard-library declarations.
The binding theorem audit covers registered claims and their definitions.
The corrected gate follows those dependencies and the logical executable entry point.
It retains every dependency, rather than deleting failing declarations from an export.

A fresh classification resolves the earlier 456-name residual as 191 unsafe definitions, 261 safe syntax definitions, and four safe time conversions.
The official exporter deliberately omits unsafe declarations by default.
The 261 syntax definitions pass all five kernels in a fresh export with no axioms.
None of the 456 names occurs in either the registered-theorem closure or the `main` closure.

The four unrelated time conversions remain outside this qualification:

- `Std.Time.Millisecond.Offset.toWeeks`
- `Std.Time.Nanosecond.Offset.toWeeks`
- `Std.Time.Week.Offset.ofMilliseconds`
- `Std.Time.Week.Offset.ofNanoseconds`

A fresh export of those four definitions passes the other four kernels.
With the Rust worker stack raised, nanoda reaches the guarded 8 GiB memory budget instead of the earlier stack overflow.
Its replay is killed without acceptance.
The original 28 GiB export collection remains retained under `.work/wt/resume-lean435/.work/tmp/`.
Its old path and timestamp logs remain insufficient to qualify current source or export bytes.
