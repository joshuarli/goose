# Scale harness

Tools that build, measure and edit large Goose programs without reading any
private workload.

| File | Use |
|---|---|
| `gen.py` | Deterministic synthetic family, its expected counts, and `--verify` against a compiler. |
| `family.py`, `edits.py`, `model.py` | The members of the family, the source edits, and the types they share. |
| `findings.py` | What multiplies specializations, as programs; checked against a compiler. |
| `edit_matrix.py` | Generates a program and each edit of it, builds and runs both, and compares the emitted C by function. |
| `cfuncs.py` | Splits emitted C into functions and compares them. |
| `parity.py` | Byte-for-byte parity of the C two compilers emit. |

## What multiplies specializations

The checker creates one specialization of a function per distinct calling
context, and groups reference roots into classes: one helper called with any
number of global and local arrays gets two specializations, not one per call
site. Each row below was produced by a small program (in `findings.py`) and
compiled with `goose -O0 --specs --check`; "printed bodies identical" is the
text `--specs` prints for the function's specializations, and "emitted C
identical" is the count of distinct implementations in `goose -O0 -o`, with
numbering of specializations and source line numbers masked and each callee
replaced by its class. `python test/scale/findings.py --goose GOOSE` repeats
the whole table and fails if the compiler disagrees.

| Id | Variation of the call | specializations | printed bodies identical | emitted C identical |
|---|---|---|---|---|
| F01 | slice argument rooted in a global, and in a local (`f`) | 2 | yes | yes |
| F02 | the same, for a body that indexes the slice (`f`) | 2 | yes | no |
| F03 | several different globals, and several locals at different depths (`f`) | 2 | yes | yes |
| F04 | two slice parameters: the same array twice, and two arrays (`f`) | 2 | yes | yes |
| F05 | two slice parameters: global or local per parameter (`f`) | 4 | yes | yes |
| F06 | two locals: first outer, first inner, or at one depth (`f`) | 3 | yes | yes |
| F07 | a writable array and a const one (`f`) | 2 | yes | yes |
| F08 | whole array and slice views of it (`f`) | 1 | yes | n/a |
| F09 | scalar reference to a global, and to a local (`f`) | 2 | yes | yes |
| F10 | an enclosing function given a global root, and a local one (`outer`) | 2 | yes | yes |
| F11 | the nested function of F10 (`inner`) | 2 | yes | yes |
| F12 | a nested function capturing a reference rebound between two calls (`rd`) | 2 | yes | yes |
| F13 | two nested functions capturing two different locals (`fa`) | 1 | yes | n/a |
| F14 | a nested function called with an optional narrowed, and not (`show`) | 2 | yes | yes |
| F15 | an optional parameter given a plain variable, and an optional one (`f`) | 2 | yes | yes |
| F16 | untyped parameters given a literal or a variable, each (`f`) | 4 | yes | yes |
| F17 | the same literal parameters given different literal values (`f`) | 1 | yes | n/a |
| F18 | two resizable references: two arrays, and one array twice, with a shrink (`f`) | 2 | yes | no |
| F19 | a `reusable` pool, and a plain array, as a resizable reference (`f`) | 2 | yes | no |
| F20 | two bound function values (`apply`) | 2 | yes | no |
| F21 | two element types (`f`) | 2 | no | no |
| F22 | a result consumed as a value and as an element run (`mk`) | 1 | yes | no |
| F23 | a return propagated to two targets (`relay`) | 2 | yes | no |
| F24 | a mutually recursive pair under a global and a local root (`ping`) | 2 | yes | yes |

What the table says about the calling context of one function:

- A reference or slice argument contributes its **root class**: a global or a
  local (F01, F03), which parameters name the **same array** (F04), the
  **relative depth** of the locals when two or more are distinct arrays (F06),
  and writable against `const` (F07). Which global, how far apart two depths
  are, and whether the argument is a whole array or a view of it do not count
  (F03, F08).
- Over `p` slice parameters the specializations are the distinct
  *root patterns*: a grouping of the parameters by array, a global or local
  label per array, and a weak order of the locals by depth. That is 8 for
  two parameters, 46 for three and 350 for four; `RootPatterns` in
  `family.py` enumerates them and `gen.py --verify` checks the count.
- A nested function is specialized once per specialization of its enclosing
  function (F10, F11), and again where a captured reference was rebound or
  an optional was narrowed at the call (F12, F14). Two nested functions that
  capture different locals are different source functions, so no variation
  (F13).
- A literal parameter is a parameter bound only by a literal: each of
  `p` untyped parameters is a literal or not, so `2^p` specializations, and
  the literals' values never matter (F16, F17). A recursive cycle needs
  explicit parameter types, so a literal parameter cannot be in one.
- Everything above except F02 leaves the emitted C identical. F02 differs
  because a global root keeps a bounds check that a local root's known length
  removes: a body that does not index its argument avoids that, which is why
  the shareable members read `.len` only.
- F18 to F23 are the cases that stay separate implementations: a body that
  caches a stack top only when the two arrays differ, a pool's freelist in the
  signature, a different callee, different element types, a result written with
  or without a header (one specialization, two emitted functions), and a
  different return target. F24, a mutually recursive pair, is identical in
  both contexts.

At -O2 the optimizer inlines small functions and removes them from the C, so
every function that the family compares is recursive, or is too long for the
inliner and called twice; nothing is inlined into a recursive function, which
is why the edit targets that must show an inlined helper use long
non-recursive callers instead.

## The family

`gen.py` without flags writes the two-context program of the original
issue and the same files as before. Flags add members:

| Flag | Adds |
|---|---|
| `--shareable N` | N copies of `RootPatterns` (`--root-params P`, 2 to 4), `ConstRefs`, `LiteralParams` and `NestedFunctions`. |
| `--distinct` | One of each case that must stay distinct, and a mutually recursive pair. |
| `--edit-targets` | The functions the source edits are about. |
| `--edit ID` | The program after an edit (`--list-edits`); implies `--edit-targets`. |
| `--verify GOOSE` | Runs the compiler over the written program and checks `expected.json`. |

`expected.json` gains `members`: per source function the number of
specializations, of distinct printed bodies, of distinct implementations in
the emitted C, whether that count is `implementations_exact` or a lower
bound, and whether the function is `inlined_at_o2`; and per must-stay-distinct
case a `pairs` entry with the reason. `--verify` checks the specializations
and printed bodies from `--specs` at -O0, the implementations from the emitted C
at -O0 and -O2 (skipping inlined functions at -O2), the total
`typechecked ok` count, the absence of warnings, and that `--jit` prints
`main.out`. The top-level counts of the original program are unchanged;
`implementations_after_sharing` is the sum of the members' implementations and
`implementations_provisional` is true while any member is a lower bound.

The original `SliceHelpers` member is such a lower bound: its helpers index
the slice, so the base compiler emits two bodies per helper at -O0 (F02), and
inlines them away at -O2. A merge that works on emitted text will reach one
body only after the context-dependent bounds-check removal is accounted for.

Must-stay-distinct members and why (each verified to give two implementations
in both -O0 and -O2 C):

| Function | Distinct because |
|---|---|
| `ds_types` | element types give different layouts and operations |
| `ds_pool_user` | a pool reference carries its freelist |
| `ds_apply` | different bound function values are different callees |
| `ds_mk` | one specialization, emitted as a value and as an element run |
| `ds_relay`, `ds_finish` | propagation to a different `return ... from` target |
| `ds_two` | distinct arrays let the body cache the second's stack top; one array cannot |

`ds_ping`/`ds_pong` are the pair that shares as a pair: two specializations
each, one implementation each. The two-parameter shrink case is accepted by
the checker with the same array twice (it reads the array it shrank, so it
must index with a check); nothing was rejected.

Not expressed as a member: a helper inlined at one call site and called at
another, which depends on the optimizer's per-site size rule. A stack top
cached under exactness in one context and not another is `ds_two`.

## Source edits

`gen.py --edit ID --out DIR` writes the program after the edit; the program
without the edit is the original. `edit_matrix.py` runs every row below. The
expected set is the source functions whose emitted code changes, with
specialization numbers and runtime-check line numbers masked; a function the
compiler writes itself is named by its C name.

| Row | Edit | Expected change |
|---|---|---|
| E02 | comment and blank line added above a function | none. only source line numbers move; no function's body changes |
| E03 | body of a leaf that is not inlined | `ed_leaf`. recursive, so no caller holds a copy |
| E04 | body of a small helper that is inlined | `ed_inl_a`, `ed_inl_b`. the helper is pasted into its two callers and has no body of its own at -O2; the caller that does not call it is unchanged |
| E05 | signature change with callers updated | `ed_sig`, `ed_sig_a`, `ed_sig_b` |
| E06 | field added to a struct | `ed_rec_user`. the function that builds the struct changes; one that never names it does not |
| E07a | a call passes a local where it passed a global | `ed_ctx_caller`, `main`. the callee reads only a length, so its body is the same under either root; the caller now owns a stack, so it takes a hidden stack argument and main's call to it changes |
| E07b | a call passes a pool where it passed a plain array | `ed_pool_user`, `ed_pool_callee`. the callee gains an instance for the pool form; the other caller keeps its plain one |
| E07c | a callee gains a shrink of its parameter | none: compile error. the caller holds a view of the array across the call |
| E08 | a specialization request added | `ed_spec_user`, `ed_gen`. its removal is the original program |
| E09a | an overload added that wins at one call site | `ed_over_u8`. the call with a u8 now resolves to the new overload; the i64 call does not |
| E09b | an import changed to a module providing the same name | `ed_imp_value` |
| E09c | an embedded file's content changed | `gs_init_globals`. the embedded bytes are static data and the global initializer is the only code that names them; the function reading the global is unchanged |
| E15a | an edit introducing a compile error | none: compile error |
| E15b | an edit introducing a new warning | none: new warning |
| E16 | an edit and its exact revert | `ed_leaf`. the edit is E03; the revert is the original program |

Not source edits of one program, so not generated: `E01` (needs a build
store), `E10` to `E14` (change the toolchain, delete or corrupt a store, or
race two builds). `E00` is the original program. `E16` runs the edit of `E03`
and then the original again, and the emitted C after the revert must equal
the first build's.

The matrix prints one JSON object per case. Fields that need code-generation
units or a build store are `null` until those exist: `frontend_phases`,
`implementation_digests_changed`, `units_changed`,
`units_per_native_invocation`, `objects_reused`, `objects_missed`,
`link_skipped`, `native_compiler_peak_rss`. Present today:
`contexts_checked`, `functions_changed` against `functions_changed_expected`,
`functions_changed_by_line_numbers_only` (functions that differ only in the
source lines their checks report, which is all an edit above them does),
`data_changed`, the compiler's wall time, CPU time and peak resident memory,
and the native compile's wall time. `--workload aincrad3 --source DIR` exits 2:
that runner does not exist.

The line numbers a body reports are part of its text, and the compiler
embeds the source path in the C: both are masked by the comparison, and
`E02` therefore changes only the line numbers.

Findings the harness made about the base compiler, beyond the table:

- A function that gains a local array takes a hidden stack argument, so its
  caller's code changes with it (`E07a` changes `main`).
- Embedded file bytes are static data; the only code that changes with them
  is the global initializer (`E09c`).

## Unit cache qualification

`units_matrix.py --goose GOOSE` runs the incremental unit-cache rows. It checks
the build's stdout and diagnostics against a clean build as well as unit text,
exit status, and executable behavior. `E16` checks the intermediate edit build
and the exact revert.

`E13` uses two observed interruption points on POSIX hosts: a FIFO blocks
completion-record publication after the object is renamed, and a compiler
wrapper blocks after a link invocation starts. The harness kills Goose only
after observing each state, then checks recovery against a clean build. The
seeded `--random N --seed S` sequence also checks expected error diagnostics,
absence of a success line on errors, warning presence, and that a damaged
object is reported and rebuilt.

`E10` checks numeric profiles, `-D`, available C compiler identities, and a
binary-only compiler identity change. Raw independent C flags, a target-only
change, and a runtime-text-only change are unavailable through the current
compiler interface: `--debug` couples numeric mode with C flags, targets are
not selectable, and runtime text is embedded in the compiler binary. Those
dimensions have `status: unavailable`; they are not passes. An E10 run exits 2
and reports `incomplete` while any such dimensions remain unavailable.

Verification status for this harness update: targeted `E13` passed with both
interruption points observed and recovery compared with clean builds. The
seeded sequence's strengthened assertions were not rerun within the three
matrix attempts; the earlier 60-step result is not evidence for this update.
E10/H2 acceptance remains parked until the unavailable dimensions are covered
or the acceptance contract is revised.
