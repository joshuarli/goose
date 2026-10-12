# Goose IR specification

**Revision:** GIR 0.2, 2026-10-12.
**Status:** design contract for the [campaign](goose-ir-campaign.md); nothing here is implemented.
**Baseline:** `62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a`.
**Companion:** [proof, conformance and qualification plan](goose-ir-validation.md).

"MUST" states the contract an implementation of this revision satisfies. The [Goose language specification](../goose_spec.md) takes precedence over this document; where its text is silent, the legacy compiler's observed behavior decides, and the disagreement is recorded (campaign, decision O2).

Part A defines the semantic representations (Typed Goose Core, GIR-H, GIR-L). Part B defines the build representations (identities, shared implementations, code-generation units, reuse). Part B applies to the legacy AST-to-C backend first and to GIR-L second; neither part depends on LLVM.

## Part A. Semantic representations

## 1. Representations and where they attach

| Representation | Purpose | Explicit in it |
|---|---|---|
| **Typed Goose Core** | Source-side meaning after resolution and specialization. Structured, typed, unoptimized. | Evaluation order, value versus place, scopes, root obligations of each checked context, effect summaries. |
| **GIR-H** | Typed CFG for language-aware transformation. | Scalar SSA temporaries, memory slots, sampled views, scopes, checked operations, evidence. |
| **GIR-L** | CFG ready for a C emitter. | Concrete layouts, frame and data-stack placement, watermarks, hidden parameters, runtime calls. |

Core is exported from the checked program after `TypeCheckProgram` and before `Optimizer` (`src/main.cpp:892-893`), the same point at which the linter's facts are built (`src/main.cpp:1440-1443`). The optimizer rewrites specialization bodies in place (`src/optimize.h:521-524`), so no later point has an unoptimized body. Export is read-only: it MUST NOT instantiate types, alter warnings, or run when no Core/GIR flag is given.

Core is distinct from GIR so that a proof about a GIR transformation cannot hide a wrong source translation. GIR-H and GIR-L share one CFG and value infrastructure and differ in which operations are legal.

Memory effects are ordered by instruction order. There is no memory SSA in this revision.

## 2. Semantic profiles

A profile is an implementation-support boundary, not a source dialect. An artifact declares exactly one profile. A program that uses a feature outside the profile is rejected by the exporter with `unsupported: <feature-id>` and a source location; it is never translated to an opaque operation. Ordinary Goose checking and the legacy backend are unaffected.

| Profile | Adds |
|---|---|
| `core-pilot` | Integer types `i8`..`u64`, `bool`; `let`/`var` locals and scalar globals; fixed arrays `T[k]` of flat fixed elements; grow-only `T[>..]` of flat fixed elements with `push`, `append`, `.len`; references `T&`/`const T&` including `.=` rebinding; slices; indexing and slicing; `if`, blocks, `while`, `for` over ranges and arrays; direct calls including recursion; nested functions with free variables; `print` of integers, booleans and string literals; `assert`, `abort`, `exit`. |
| `core-shrink` | Grow-shrink `T[>..<]`; limited `T[..k]`; `pop`, `pop_n`, `resize`, `clear`, whole assignment of a resizable; flat fixed structs. |
| `core-construction` | Variable arrays `T[]` and string values; grow-only arrays of variable elements; nonfixed by-value parameters and results built in the receiver's storage; `copy`; named results; `return … from`. |

Excluded from all three, each with its own feature id: references or slices stored in fields or elements (`stored-reference`), optionals, ADTs, relative references, pools and `reusable`, `varint`, floats, elementwise arithmetic, generics beyond what specialization already resolved, function values, threads, `extern fn`, serialization, declarations without initializers, temporaries viewed as slices, zero-size values.

Storing references only in variables, parameters and results is the single largest simplification: every root is exact, and no holder analysis is needed. Lifting it is a later profile.

## 3. Identities

Module-local dense ids: `FnId`, `VarId`, `TypeId`, `ScopeId`, `BlockId`, `ValueId`, `SlotId`, `OriginId`. They are deterministic for identical input and are never used across sessions. Cross-session identities are the stable keys of Part B (§15). Native addresses, hash-map iteration order and AST allocation order are never serialized.

An origin names a source file, line and the source node kind of the construct an operation came from. A synthesized operation records the construct responsible for it. Origins do not decide linter finding identity; the linter's own fingerprints do.

## 4. Typed Goose Core

### 4.1 Types

```text
IntTy ::= i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64
Mut   ::= mut | const
Ty    ::= int IntTy | bool | unit
        | arr Ty k                  -- T[k], k ≥ 1
        | grow Ty                   -- T[>..]
        | ref Mut Ty | slice Mut Ty -- T&, T[:]
        | tuple [Ty]                -- multiple results only
        -- core-shrink
        | growshrink Ty | limited Ty k | struct StructId
        -- core-construction
        | varr Ty
```

`flat fixed` means built from `int`, `bool`, `arr` and `struct` only. `grow`, `growshrink` and `varr` types occur only as the type of a variable, a by-reference parameter's pointee, or (construction profile) a by-value parameter or result.

### 4.2 Values and memory

```text
RootInst ::= global VarId | local ActId ScopeInst VarId
Obj      ::= scalar Val | fixed [Obj] | resizable [Obj] | limitedObj k [Obj] len | record [Obj]
Loc      ::= (RootInst, [Nat])              -- root and selector path
Val      ::= int IntTy Int | bool Bool | unit | arrv [Val] | recv [Val]
           | ref Loc | slice Loc start len | tuple [Val]
Store    ::= RootInst ⇀ Obj
```

`ActId` is fresh for every call and `ScopeInst` for every block entry, including each loop iteration. Leaving a scope removes its root instances from the store. A `slice Loc start len` is a run of `len` elements of the array object at `Loc`. An access through a `Loc` whose root is absent or whose path is out of range is a **fault**, which is neither a Goose abort nor a rejection: it is the event the safety theorem proves unreachable for validated programs.

A `limitedObj` keeps every slot written so far; only `len` changes on `pop`. A reference to a popped slot stays valid and may read a later value of the same type. A `resizable` object's elements above its new length cease to exist on shrink.

Integers are mathematical integers with a range invariant for their type. Arithmetic is defined on `Int` followed by an explicit wrap; bitwise and shift operations are defined by conversion to and from a bit vector of the type's width. Signedness is part of the type.

### 4.3 Program structure

```text
Module  ::= schema, profile, numeric, sources, types, globals, impls, contexts, entry, origins
Impl    ::= name, params, results, vars, body, summary          -- executable; carries no roots
Context ::= impl ImplId, decl DeclKey, roots RootAnn             -- one checked specialization
Param   ::= VarId, Ty, mode (byValue | byRef)
RootAnn ::= var-roots (VarId ⇀ [RootRef]), result-roots [[RootRef]]
RootRef ::= var VarId | param Nat
```

The split between **implementation** and **context** is deliberate. An implementation is everything execution needs. A context is one checked specialization of the source function: it points at an implementation and carries the root annotations the validator checks for that specialization. Several contexts may point at one implementation (§16). Execution never reads a context.

Nested functions are closure-converted by the exporter: each free variable becomes a trailing by-reference parameter, in the order the legacy backend passes them (language spec C.3). Core has no nested functions.

### 4.4 Syntax

```text
Place ::= var x | deref e | elem v e | field p n
View  ::= viewOf p            -- p : arr | grow | growshrink | limited; length sampled now
        | viewVal e           -- e : slice; the slice's own run
Bound ::= expr e | fromEnd e | omitted
Expr  ::= lit c | read p | refOf m p | sliceOf m v lo hi | lenOf v
        | un op e | bin op e₁ e₂ | cmp op e₁ e₂ | and e₁ e₂ | or e₁ e₂ | not e
        | conv kind τ e                      -- widen | as | asUnchecked
        | call ContextId [Arg]               -- Arg ::= byVal e | byRef m p
        | push p e | ifE e b b | blockE b | arrLit [e] | arrFill e k
Stmt  ::= let x e | assign p e | assignOp op p e | rebind x e | expr e | append p v
        | ifS e b b? | while e b | forRange x lo hi b | forEach x idx? v byRef b
        | ret e? | break | continue | print [PrintArg] | assert e | abort msg | exit e
        -- core-shrink
        | pop p | popN p e | resize p e fill? | clear p | assignWhole p e
Block ::= [Stmt] then optional value Expr
```

Reference transparency, overload selection, implicit conversions, member-call receivers and array-to-slice coercions are already resolved: Core records `read (deref …)`, the selected callee and each conversion explicitly.

### 4.5 Evaluation

The semantics is one total, fuel-indexed function

```text
eval : Fuel → NumericProfile → Module → Result
Result  ::= done Outcome Trace | timeout Trace | fault FaultKind
Outcome ::= returned | aborted AbortKind OriginId | exited Int
Trace   ::= bytes written to standard output, in order
```

and is the only definition of Core behavior. It is deterministic. `timeout` means the fuel ran out and says nothing about divergence.

Normative ordering rules, each of which has fixtures:

| Rule | Statement |
|---|---|
| `E-LTR` | Operands, arguments and literal elements evaluate left to right. A by-value operand is read when it is evaluated. |
| `E-INDEX` | `elem v e`: evaluate `v` to a view `(loc, start, n)`; then `e` to `i`; abort `index_oob(i, n)` unless `0 ≤ i < n`; the place is `loc/(start+i)`. The length is the sampled `n`, never a later one. |
| `E-SLICE` | `sliceOf m v lo hi`: sample `v`; evaluate `lo` (default 0) then `hi` (default `n`; `fromEnd k` is `n − k`); abort `slice_oob` unless `0 ≤ lo ≤ hi ≤ n`. |
| `E-ASSIGN` | Resolve the destination place, including its checks, then evaluate the right side, then store. |
| `E-ASSIGNOP` | Resolve the destination, read its old value, evaluate the right side, combine, store. |
| `E-CALL` | Evaluate arguments left to right (`byRef` resolves a place), then enter a fresh activation. |
| `E-PUSH` | Resolve the owner, evaluate the element, append, and yield a reference to the new element. |
| `E-SHORT` | `and`/`or` evaluate the right side only when needed. |
| `E-RANGE` | `forRange` evaluates both bounds once. An empty or reversed range runs no iteration. |
| `E-EACH` | `forEach` over a resizable owner tests the current length before each iteration; over a slice, fixed or limited array it uses the length sampled at entry. |
| `E-SCOPE` | Leaving a block by fallthrough, `break`, `continue`, `ret` or propagation removes that block's roots. An abort removes nothing and ends the program. |
| `E-WHOLE` | `assignWhole p e` truncates `p` to empty, then builds `e` into it. |

`E-INDEX` and `E-LTR` were confirmed on the baseline compiler: `short[grow_and_index(short)]`, where the index expression pushes onto `short` and returns 1, prints the callee's output and then aborts with `index 1 out of bounds (length 1)`.

`print` writes its arguments' renderings and a newline: integers in decimal, booleans as `true`/`false`, literal text verbatim.

Abort kinds and the runtime text they correspond to: `div_zero` (`division by zero`), `div_overflow` (`integer overflow in division`), `index_oob` (`index I out of bounds (length N)`), `slice_oob` (`slice bounds out of range`), `assert`, `user_abort`; debug profile only: `int_overflow`, `cast_range`; `core-shrink`: `pop_empty`, `pop_n_range`, `resize_negative`, `capacity`. An abort exits with status 1 after writing `goose runtime error: <text> (<file>:<line>)` to standard error.

### 4.6 Validation

`validate : Module → Except Rejection Unit` is independent of the C++ checker. It trusts no exported annotation: root annotations and effect summaries are checked, not assumed. It checks every **context** separately, including contexts that share an implementation.

| Rule | Check |
|---|---|
| `V-TYPE` | Every expression, place and statement is well typed; conversions are legal; arities match. |
| `V-MUT` | Writes go through `mut` places; `let` variables are not reassigned; `rebind` targets a `var` of reference or slice type. |
| `V-ROOT` | A value with root set ρ may initialize, be assigned to, or rebind variable `r` only if ρ ⊆ roots(`r`) and every member of ρ outlives `r`. `param i` and globals outlive every local. A local `y` outlives `r` when `y`'s scope is `r`'s scope with `y` declared first, or an enclosing scope in the same implementation. |
| `V-BLOCK` | The value of a block or `ifE` is not rooted at a variable declared inside it. |
| `V-RESULT` | A returned reference or slice is rooted only at `param i` or globals, within the declared result roots. |
| `V-CALL` | At a call, each `param i` in the callee context's result roots is replaced by the actual argument's roots; the argument's mutability satisfies the parameter's. |
| `V-SUMMARY` | Each implementation's effect summary is closed: the effects of its body, computed with its callees' summaries, are contained in it. Recursion needs no iteration, because closure is checked, not computed. |
| `V-SHRINK` | At a shrink of the array rooted at `a`, no variable in the demand set has `a` among its roots. The demand set is every variable named in an operand evaluated later in the statement, in a later statement of an enclosing block in the same implementation, or anywhere in an enclosing loop body. |
| `V-WHOLE` | The right side of `assignWhole p e` neither names a variable rooted at `p`'s root nor calls an implementation whose summary reads, writes or resizes that root. |

`V-SHRINK` is at most as permissive as language spec §5.1. Where the frontend accepts a shrink through §5.1's `return`/`break` exception and the validator does not, the exporter reports `unsupported: shrink-exit-exception`.

An effect summary records, over the implementation's parameters and the globals: reads, element writes, growth, shrink, reference rebinding, possible abort, output, and the set of nonlocal targets it may propagate. Unknown is a distinct value that implies every effect.

## 5. Numeric and failure semantics

From language spec §6.2 and §6.3; the Euclidean remainder and shift masking rows were confirmed on the baseline compiler (`-5 % 3` is `1`; `(-128 as i8) >> 9` is `-64`).

| Operation | Rule |
|---|---|
| Arithmetic width | At the operands' common type; no promotion. |
| Unsigned `+ - *` | Modulo `2^w` in every profile. |
| Signed `+ - *` and negation | Release: two's-complement wrap. Debug: abort `int_overflow` when the mathematical result is out of range. |
| `/` | Truncating. Zero divisor aborts `div_zero` in every profile. `i64.min / -1` aborts `div_overflow` in every profile. A narrower signed minimum divided by `-1` is an ordinary overflow: debug abort, release wrap. |
| `%` | Euclidean: result in `[0, \|b\|)`. Zero divisor aborts. `min % -1` is `0`. |
| Shifts | Count masked to `0..w-1`. Signed `>>` replicates the sign bit; unsigned shifts in zeroes. |
| `as` between integers | Debug: abort `cast_range` on value change. Release: wrap to the target width and sign. |
| `as!` | Wrap in every profile. |

Debug overflow checks attach to operations as executed. The optimizer may regroup or drop a signed operation, so only the unoptimized debug profile is compared exactly against Core; an optimized debug build is compared exactly on mandatory aborts and on release-visible results.

Floats are outside every profile in this revision. For the record that a later profile needs: a float-to-integer cast truncates toward zero and wraps modulo `2^64` into the target in release and for `as!`; NaN gives 0; a debug `as` aborts on value change; the language spec does not say what an infinity converts to.

A mandatory abort is never removed because its result is unused.

## 6. Resizable storage (`core-shrink`)

Growth never invalidates a reference or slice. A shrink removes elements above the new length of a `grow` or `growshrink` object and keeps every written slot of a `limited` object. `pop` on an empty array, `popN` with a negative count or more than the length, and `resize` to a negative length abort before changing anything. Exceeding a limited array's capacity aborts `capacity` before writing.

Whole assignment is a shrink followed by construction (`E-WHOLE`, `V-WHOLE`).

## 7. Construction and nonlocal exits (`core-construction`)

### 7.1 Construction

A nonfixed value exists only where the language's construction contexts provide storage (language spec §4.2). In Core a construction context is a **destination** `(owner place, request)` with `request ::= value | elementRun`. A constructing expression — a literal, a call with a nonfixed result, `copy`, or an `if`/block choosing among such — evaluates directly into its destination. Core's values make the result observable; the **construction trace** makes the manner observable.

The construction trace is a second, separately compared event list: `begin(dest)`, `write(dest, index)`, `publish(dest)`, `copy(src, dest)`, `relocate(dest, reason)`, `stage(dest, reason)`, `abandon(dest)`. The contract over it:

| Rule | Statement |
|---|---|
| `C-ONCE` | Every initializer expression is evaluated exactly once. |
| `C-DIRECT` | A fresh result for a `grow` receiver produces no `stage` and no `copy` event. |
| `C-RELOCATE` | `relocate` is permitted only with reason `header-removal` (a value-form result delivered as an element run). |
| `C-STAGE` | `stage` is permitted only for a `limited` receiver whose result length is unknown before evaluation; nothing is written outside the receiver's free slots before the capacity check. |
| `C-NOGROW` | While a destination inside array `a` is open, nothing grows or shrinks `a`. This is a validation rule, restricted to nonfixed elements and whole assignment; a pushed fixed element is evaluated before the push and is unrestricted. |
| `C-NAMED` | If every `ret` of a nonfixed result returns the same local at its last use, that local's destination is the result destination and returning it emits no event. Each other returned local emits one `copy`. |
| `C-ABANDON` | An exit taken while a destination holds a partial value emits `abandon` for exactly the partial part. Elements published earlier stay published; output already written stays written. The exit's own value, if built behind the partial part, emits one `relocate` with reason `exit-value`. |

Construction is not a transaction.

### 7.2 Nonlocal return

`return E from f` returns `E` as the result of the **innermost active call** of a function in `f`'s target set (language spec §7.9). The target set is fixed at the `return` statement; the catching activation is whichever activation of a function in that set is nearest on the call stack. Core therefore needs no activation-bound capability: a body result is

```text
BodyResult ::= normal Val | returning Val | escaping TargetId Val | breaking | continuing
```

and a call whose callee yields `escaping t v` yields `returning v` if the caller's implementation is a member of target `t`, and `escaping t v` otherwise. Every scope left on the way is removed by `E-SCOPE`. A destination handed down by the target survives because it belongs to the target's caller.

This was confirmed on the baseline compiler with a recursive `descend` three levels deep in which the deepest level calls a helper that executes `return 20 from descend`: the deepest activation returns 20 and the level above resumes normally.

A static target id is thus an exact implementation, and matches the legacy protocol (one thread-local discriminant, language spec C.3). A plain `return` inside a function-value body is the same mechanism with the enclosing named function as target.

## 8. GIR-H

### 8.1 Functions

A function has a signature, a slot table, a scope tree, a block table, an effect summary and an origin. A **slot** is memory-resident storage for one source variable: type, owning scope, and source `VarId`. Every source variable lowers to a slot; SSA values are temporaries. Promotion of slots to SSA is not part of this revision.

Blocks have typed parameters, an ordered instruction list and one terminator. Definitions dominate uses.

```text
VTy ::= int IntTy | bool | unit | ref Mut Ty | slice Mut Ty | view Ty | tuple [VTy]
```

A `view` is a sampled `(region, start, length)`. It is an SSA value only: it cannot be stored, passed or returned.

### 8.2 Instructions

| Family | Operations | Contract |
|---|---|---|
| Constants | `const τ c` | |
| Integer | `int.add`, `int.sub`, `int.mul`, `int.neg`, `int.div`, `int.mod`, `int.and`, `int.or`, `int.xor`, `int.not`, `int.shl`, `int.shr`, `int.cmp pred` | §5 at the stated type. `int.div`/`int.mod` may abort. |
| Boolean | `bool.not` | Short-circuit is control flow. |
| Conversion | `conv kind τ→τ'` | `widen`, `as`, `as_unchecked`. |
| Addresses | `slot.addr s`, `global.addr g`, `ref.elem r n`, `ref.field r n` | Yield `ref`. |
| Memory | `load r`, `store r v` | Fixed types only. |
| Views | `array.snapshot r`, `slice.view v`, `view.len v`, `view.slice v lo hi`, `array.len r` | `array.snapshot` samples region and length. `view.slice` aborts `slice_oob`. |
| Indexing | `array.index.checked v i`, `array.index.proven v i` | Checked aborts `index_oob`. Proven requires evidence (§10). |
| Growth | `array.push r v`, `array.append r v` | |
| Shrink | `array.pop r`, `array.pop_n r n`, `array.resize r n fill?`, `array.clear r` | Abort per §6. |
| Scopes | `scope.enter S`, `scope.leave S` | Slots of `S` are usable only between them. |
| Calls | `call f(args)` | Legal only when `f`'s summary propagates no nonlocal target. |
| Output | `print parts` | |
| Construction | `dest.open r request`, `dest.write d v`, `dest.publish d`, `dest.abandon d`, `dest.pass d` | Path-linear: every path from `dest.open` reaches exactly one of `publish`, `abandon` or `pass`. |

| Terminator | Contract |
|---|---|
| `br b(args)` | Arity and types match. |
| `condbr c, t(args), e(args)` | `c : bool`. |
| `ret vals` | Every scope of the function has been left. |
| `invoke f(args) normal b(vals) escape e(target, val)` | Required when `f` may propagate a nonlocal target. |
| `escape target val` | Propagate after leaving every scope of the function. |
| `abort kind origin` | Defined termination. |
| `exit v` | Program exit. |

`unreachable` is not in this revision.

### 8.3 Lowering from Core

Lowering is a function of an implementation alone; it never reads a context. Each Core rule maps to a fixed instruction sequence, so evaluation order is the instruction order: `E-INDEX` becomes `array.snapshot`, the index computation, `array.index.checked`; `E-ASSIGN` computes the destination reference before the right side. `forRange` puts its induction variable in a block parameter of the loop header, with the bound computed before the loop. A Core call to context `c` becomes a call to `c`'s implementation.

## 9. GIR-H verifier

The C++ verifier runs after lowering and after every pass on the `gir` pipeline; it is not optional there. Diagnostics are compiler errors, not lint findings.

| Code | Checks |
|---|---|
| `GIR-V001` module | Schema, profile, entry points, resolved symbols, size limits. |
| `GIR-V010` types | Operand and result types of every operation; arity. |
| `GIR-V020` CFG | One terminator per block; edge argument types; dominance. |
| `GIR-V030` storage | A slot address is taken only inside its scope; stores go through `mut`; loads and stores have fixed types. |
| `GIR-V040` scopes | `scope.enter`/`scope.leave` balance on every path and nest as the scope tree; `ret` and `escape` occur with no scope entered. |
| `GIR-V050` effects | Summaries are closed (as `V-SUMMARY`); `call` versus `invoke` agrees with the callee's summary. |
| `GIR-V060` construction | Destination linearity; no `dest.write` after publish; `C-NOGROW` on the open destination's owner. |
| `GIR-V070` exits | Every `invoke` escape edge leaves the scopes it exits; a function in the target set of `t` handles `t`. |
| `GIR-V080` evidence | Every `array.index.proven` is justified by a valid fact certificate (§10). |
| `GIR-V090` stage | Only operations legal for the stage; in GIR-L, resolved layouts, placements and hidden parameters. |
| `GIR-V100` origins | Every operation that can abort or that corresponds to a source statement has a valid origin. |

Reference lifetime is not re-derived on GIR. It is established on Core by `validate`, and carried to GIR by the lowering theorem for the profiles that theorem covers. A verifier that checks only SSA and types MUST NOT be described as checking storage safety.

## 10. Evidence: bounds facts

`array.index.proven v i` is legal only if the function carries a **fact certificate**: a set of facts for the entry of every block. The checker makes one pass and accepts if every block-entry set follows from its predecessors.

```text
Fact ::= ge0 %i | lt %i %n | lenGe Owner %n | viewLenGe %v %n
Owner ::= slot SlotId | global GlobalId
```

Generation, each with a soundness lemma in Lean:

| Rule | Premise | Fact |
|---|---|---|
| `F-CONST` | `%c = const i64 k`, `k ≥ 0` | `ge0 %c` |
| `F-CMP` | true edge of `condbr` on `int.cmp slt i64 %a %b` | `lt %a %b` |
| `F-GE` | true edge of `condbr` on `int.cmp sge i64 %a %z`, `%z` a zero constant | `ge0 %a` |
| `F-NEXT` | `%j = int.add i64 %i %one`, `%one` the constant 1, with `ge0 %i` and `lt %i %n` | `ge0 %j` |
| `F-LEN` | `%n = array.len r`, `r` the address of owner `O` | `lenGe O %n`, `ge0 %n` |
| `F-SNAP` | `%v = array.snapshot r`, `r` the address of `O`, with `lenGe O %n` | `viewLenGe %v %n` |
| `F-FIXED` | `%v = array.snapshot r`, `r : ref (arr T k)`, `%c = const i64 k'`, `k' ≤ k` | `viewLenGe %v %c` |

`F-NEXT` is sound without a separate overflow premise because `%i < %n ≤ i64.max`.

Kills: an instruction defining a value removes every fact that mentions it; entering a block removes facts about that block's parameters before the edge's substituted facts are added; an instruction or call whose effect may shrink `O`, and `scope.enter` of `O`'s scope, remove every `lenGe O _`. An unknown effect shrinks everything.

`array.index.proven %v %i` requires `ge0 %i`, `lt %i %n` and `viewLenGe %v %n` for one `%n` at that instruction. This is the rule that a bound on a grow-only array's length holds across every push (language spec §5.1), stated so that a shrink, an unknown call or a re-entered scope visibly breaks it.

A certificate holds within one implementation. It uses no fact about callers. An implementation shared by several contexts (§16) therefore needs no per-context evidence. A pass that wants entry facts derived from call sites MUST derive them from every call site of the implementation, not of one context.

A rule is added only with its soundness lemma.

## 11. GIR-L

### 11.1 Placement

| Core storage | GIR-L placement |
|---|---|
| Fixed slot | A frame member. |
| `grow`/`growshrink` slot | A header `{base, len}` in the frame and an element region on a data stack. |
| Global | A member of its module's globals segment (§17.4); a resizable global's elements on a stack of its own. |
| `ref` to fixed storage | An address. |
| `ref` to a resizable | The header's address and its stack: two parameters. |
| `slice` | `{data, len}`: two parameters. |

The stack plan in this revision gives every resizable slot its own data stack, numbered within the function from a base passed as a hidden argument, as the legacy backend does (`gs_sp + k`, `src/codegen_stacks.h:11-16`). Sharing a stack between slots of disjoint lifetime is not part of this revision. A function in a call cycle whose resizable slot is live across a call into the cycle is `unsupported: recursive-resizable`.

Placement obligations checked by `GIR-V090`: at most one live resizable per stack; a resizable's elements top its stack for its whole life; `scope.leave` restores the watermark recorded at `scope.enter`; a watermark restore never crosses a destination owned by a caller.

### 11.2 Operations

GIR-L replaces views, checked indexing, growth, shrink, scopes and construction with: address arithmetic with explicit element size; `cmp` and `condbr` to an `abort` block for each check; `stack.mark s`, `stack.release s m`, `stack.bump s n`; `header.load`/`header.store`; `bytes.copy` and `bytes.move` with explicit overlap; `runtime.call name` for a closed list of runtime entry points. No view, scope, destination or unresolved layout remains.

Nonlocal exits lower to the existing protocol: a thread-local discriminant, set at the `return … from`, tested after each `invoke`, cleared at the catch.

### 11.3 C emission

The emitter consumes GIR-L directly; it does not rebuild the AST. It emits one statement per instruction in order and never depends on C argument evaluation order. Signed wrapping uses unsigned arithmetic. Aborts call the runtime's existing entry points (`gs_idxfail`, `gs_divfail`, `gs_divovf`, `gs_ovf`, `gs_abort`, `gs_exit`, `src/runtime/runtime.h:157-176`); debug-checked arithmetic and conversions use its existing helpers (`gs_add_i64`…, `gs_rangechk`…). Each reused entry point is listed in the trust ledger as assumed, not proved.

The emitter produces instance text through the unit interface of §17, so partitioned and single-file output are the same code path with different assembly.

## 12. Serialization

Core and GIR are written by the C++ compiler and read by the Lean tool. The C++ compiler has no reader for either: malformed-artifact handling is the Lean decoder's job, and the C++ verifier is tested on in-memory modules.

Encoding: JSON in which every record is an **array** whose first element is a tag string, with fixed arity per tag. There are no objects, so there are no unknown or duplicate keys to police; this matters because the pinned Lean JSON parser accepts duplicate object keys silently. Table indices and counts are JSON integers below `2^31`. Program integer constants are decimal strings. Output is deterministic: tables in id order, no insignificant whitespace.

The decoder rejects, with `malformed`: an unknown tag, a wrong arity, a wrong element type, an out-of-range index, a constant outside its type's range, trailing data, input over 64 MiB, nesting deeper than 256, more than `2^24` nodes in one function.

The schema string names the representation and revision (`goose-core/0.2`, `gir-h/0.2`, `gir-l/0.2`). A reader accepts only the exact string it implements. Artifacts are not persisted across compiler versions, so there is no migration.

## Part B. Build representations

## 13. The four costs

A large program's edit-build-verify loop pays four separable costs, and no single mechanism addresses all of them.

| Cost | What it is | Addressed by | Not addressed by |
|---|---|---|---|
| (a) Frontend | Parse, resolve, check and specialize every context, optimize, on every build. | No-op short-circuit (§19.2); checked-result reuse (§19.4, deferred); checking once per implementation rather than per context (deferred, §16.6). | Sharing after checking; partitioning; object reuse; Lean; serialized GIR; LLVM. |
| (b) Emitted code | Distinct emitted bodies and inline expansion. | Shared implementations (§16). | Object reuse (it only hides (b) on warm builds); partitioning. |
| (c) Native compile | The C compiler re-optimizing unchanged code. | Units (§17) with object reuse (§19.1); fewer bytes from (b). | Sharing alone on a warm build; Lean; serialized GIR. |
| (d) Link and driver | Linking, process startup, file writing. | Link skip (§19.1); batched and parallel compiler invocations (§17.6). | Everything else. Partitioning increases (d). |

Lean contributes proofs about when sharing and reuse are safe (validation plan TH-SHARE-01, TH-REUSE-01). It removes none of the four costs. Direct LLVM emission could change the constant factor of (c) and nothing else, and is not part of this revision.

## 14. What the baseline does

Verified at the baseline revision.

- The specialization reuse test compares: lexical parent, escape state, narrowed optionals, the outer-variable state the body read, concrete argument types, unmentioned type bindings, literal parameters, bound function values, per-argument root descriptors (class, writability, pool, grow-shrink, slot-read, byte-view, held-exact, unknown), grow-shrink element types and one-array classes, the depth key, slot views, and concrete `return from` targets (`src/typecheck_calls.h:1520-1587`; table at `docs/implementation.md:291-301`).
- Of the root descriptors, code generation reads only the pool form, which changes the signature (`src/codegen_frames.h:19-21`, `:303-305`). It also reads `exact` and `concrete`, which are not in the key and are merged over call sites (`src/typecheck_calls.h:1580-1587`), to decide which stack tops a body caches (`src/codegen_emit.h:262-300`). Class, depth key, writability and the rest have no code-generation reader.
- Stack identities are hidden arguments, not constants baked into a body (`src/codegen_frames.h:306-312`).
- Bounds-check elimination seeds a body's entry facts from all call sites of that specialization (`src/bce.h:1686-1712`), and inlining reads a program-wide use count (`src/optimize.h:529`, `:746`). Both are properties of the caller set, not of the body.
- Emitted bodies are never merged (`src/codegen_frames.h:97-98`).
- Emitted names embed creation-order numbers: the specialization index (`src/codegen_frames.h:103-107`), string and blob literal counters (`src/codegen_values.h:1330`, `:1347`), a dense nonlocal-target counter (`src/codegen_frames.h:112-113`) and first-come type names (`src/codegen_types.h:372-378`, `:564-573`). One added specialization can rename unrelated code.
- `goose build` rewrites one C file and makes one compile-and-link call; no program object is kept (`src/build.h:139-166`, `:229`). Only the runtime object and native packages are cached, and a published runtime object is trusted on existence (`src/build.h:170`).
- All globals are members of one struct (`src/codegen_emit.h:689-716`).
- No phase is timed. `typechecked ok: N specialization(s)` counts every specialization created, dead ones included (`src/main.cpp:899-903`).
- A runtime diagnostic carries the file, the line, the values and an operand type name; never a function or instantiation name (`src/runtime/runtime_impl.h:50-72`).

Consequence: checked-context count is an upper bound on distinct bodies and says little about how many are distinct. The count of distinct bodies is unknown until measured (§20).

## 15. Identities

Six concepts that the baseline conflates in one specialization index.

| Concept | Identity | Stable across | Changes when |
|---|---|---|---|
| Source declaration | `DeclKey` | Unrelated edits, reordering, other files. | The declaration is renamed, moved to another module or namespace, or its written parameter types change. |
| Checked semantic context | `ContextKey` | Unrelated edits. | Any dimension the checker compares changes. |
| Emitted code instance | `InstanceKey` | Body edits. | The declaration or a lowering-relevant dimension changes. |
| Canonical implementation | `ImplDigest` | Nothing but equal content. | The lowered body, a callee's symbol, a layout or a constant it uses changes. |
| Code-generation unit | `UnitKey` | Body edits; instances added to other units. | The partition rule moves the instance. |
| Artifact | fingerprints (§18) | | Any declared input changes. |

`DeclKey` is the module's import identity, the namespace path, the declaration name, the canonical spelling of its written parameter types, and for a nested function or block literal the enclosing `DeclKey` and its ordinal among same-named siblings. It contains no line number and no table index.

`ContextKey` is the `DeclKey` and a canonical serialization of every dimension in §14's reuse test. A caller-local root is named by the caller's `ContextKey` and the root variable's ordinal in its declaration, never by a pointer.

`InstanceKey` is the `DeclKey` and the **lowering key**: the dimensions that can change the lowered body or its signature. It is used for naming only; it is never trusted to imply body equality.

```text
LoweringKey ::= concrete parameter and result types (by TypeKey)
              , physical form of each reference parameter (address | header+stack | pool reference)
              , destination request of each nonfixed result (value | elementRun)
              , capture list (the hidden reference and stack parameters)
              , bound function values (by InstanceKey) and literal parameters
              , nonlocal targets it may propagate and those it catches
              , consumed assumptions
```

**Consumed assumptions** are the context-dependent facts an optimization actually used for this body: entry facts taken from call sites, root disjointness or exactness used to remove a check or cache a stack top, and each inlining decision. They are recorded by the pass that uses them. A fact that was available and unused is not in the key.

`TypeKey` is structural for built-in type constructors and a `DeclKey` plus argument `TypeKey`s for nominal types.

The instance's link symbol is derived from the `InstanceKey`: a sanitized readable prefix and 16 hex digits of its digest. It is not derived from the body, so a body edit does not rename the instance or touch its callers. Collisions among the program's symbols are detected at compile time and are a compiler error.

Digests are SHA-256, implemented in the compiler; names use a 64-bit prefix, stored digests 128 bits.

## 16. Shared implementations

### 16.1 Invariant

Every checked context is checked. Sharing merges emitted bodies after checking and changes nothing about which programs are accepted, which diagnostics are produced, or which contexts the linter counts.

### 16.2 Criterion

Two instances share an implementation when their **canonical lowered bodies** are equal. The canonical lowered body is the instance's lowered form — C text on the legacy backend, GIR-L on the GIR backend — with its own symbol replaced by a placeholder and every callee named by its implementation. The check is structural equality of that form: bounded, decidable, and not an attempt at program equivalence. Two bodies that differ in one retained check, one inlined call or one source line are different.

Classes are computed bottom-up over the call graph's strongly connected components. A self-call is a placeholder. For a component of several instances, members are ordered by `InstanceKey`, intra-component calls are replaced by member ordinals, and two components are equal when their ordered members are pairwise equal. A component in which two members have the same `DeclKey` and lowering key is not merged with any other.

A class is named by the smallest link symbol among its members.

### 16.3 Why equality of the lowered form is the right first criterion

Everything that could make sharing unsafe is materialized in the lowered body. A check removed in one context and kept in another gives different bodies. A different physical reference form gives a different signature. A different source line gives a different diagnostic argument. Nothing has to be argued about which key dimensions are irrelevant; the dimensions that turn out irrelevant are the ones that leave no trace in the body.

The cost is that context-dependent optimization blocks sharing: two contexts that would lower identically without bounds-check elimination or inlining may differ after it. §16.5 addresses that as a second, measured step.

### 16.4 Must share and must stay distinct

Each row is a member of the synthetic family (validation plan §9) with an asserted outcome.

| Case | Outcome | Reason |
|---|---|---|
| One function called with a global root and with a local root (issue #9's `first`) | Share | Roots of slices and plain references leave no trace in the body. |
| Same roots at different depth keys | Share | Depth is a checking fact. |
| A writable and a read-only reference to the same type | Share | Writability is a checking fact. |
| Free variable bound to different outer locals of one type | Share | Captures are hidden reference parameters. |
| Different concrete argument types | Distinct | Different layouts and operations. |
| A `reusable` pool parameter versus a plain resizable reference | Distinct | The pool form changes the signature. |
| Different bound function values | Distinct | Different callees. |
| A result requested as a value versus as an element run | Distinct | The header is written or not. |
| Different nonlocal targets propagated or caught | Distinct | Different discriminant tests. |
| Two parameters rooted at different arrays in one context and at one array in another, where the body indexes one after growing or shrinking the other | Distinct when a check was removed in the first; shared when it was kept in both | A removed check is valid only where its fact holds. |
| A stack top cached under exactness in one context and not in another | Distinct | The cache changes the body. |
| A helper inlined at one context's call site and called at another's | Distinct | Inlining is per site. |
| Mutually recursive pair under two root contexts | Share, as components | §16.2. |

### 16.5 Sharing before optimization

Sharing after lowering does not reduce optimization or emission work, and loses contexts that differ only by a context-dependent optimization. The second step merges instances before the optimizer when their checked bodies are equal once the checking-only dimensions are erased (root class, depth key, writability, narrowing, the outer-variable state read) and their lowering keys, less consumed assumptions, are equal. The optimizer then runs once on the merged instance with the union of its call sites, so every entry fact and every inlining decision is derived for all admitted contexts, and a fact that fails in one context is unavailable to all.

This step asserts that the erased dimensions do not affect lowering. That assertion is validated on every build in validation mode: each member is also lowered alone with optimization off, and its canonical body MUST equal the merged instance's unoptimized body. A mismatch is a compiler error naming the dimension, not a silent fallback.

The step is taken only if the cost report shows that context-dependent optimization blocks a material share of otherwise equal bodies (campaign, item `O2`).

### 16.6 What sharing does not do

Sharing reduces emitted bodies. It does not reduce the number of contexts checked, and so does not reduce frontend cost (a). Reducing checking work needs the checker to check a body once against root parameters and each call site against the result — the structure of Core's `validate` (§4.6), which the Lean safety theorem shows sound for the profiles. Applying that structure to the production checker is deferred (campaign, deferral `X1`).

## 17. Code-generation units

### 17.1 Scope

A unit is one C translation unit holding some of a whole program's instances. Units partition the output of a whole-program compiler. They are not separately compiled modules: every unit is generated from a full check of the whole program, and no unit has a source-level interface. A module or package system with separate checking is outside this document.

Single-file output remains: `-o`, `--standalone`, `--jit` and the bundled linter build produce the same single file as the baseline, byte for byte. Units are an opt-in mode of `goose build`.

### 17.2 Assignment

`UnitKey` is the declaring module of the instance's `DeclKey` and a shard number. A module has `2^s` shards, with `s` the smallest value that keeps the module's emitted bytes per shard at or under the target size; the shard is the top `s` bits of the instance symbol's digest. An instance added anywhere changes one unit. A module that crosses a size threshold splits or merges only its own shards. The target size is set from measurement (campaign, item `B3`); the proposed starting value is 512 KiB of C.

Each implementation is emitted exactly once in the program, in the unit of its class name.

### 17.3 Unit contents

A unit's text is, in order: the unit's defines; the runtime header; the type declarations it uses, in `TypeKey` order; `extern` declarations of the globals segments, literals, location tables, callees and nonlocal channels it uses, in symbol order; its instances in symbol order. A unit declares only what it uses. There is no header shared by all units other than the runtime header, which changes only with the compiler.

C type names are derived from `TypeKey`, not from request order. The same struct may be declared in several units.

### 17.4 Whole-program entities

| Entity | Unit mode |
|---|---|
| Instances | External linkage, hidden visibility, stable symbol (§15). |
| Small helpers under a size threshold | `static` in each unit that uses them; no cross-unit dependency. |
| Globals | One segment struct per module, defined in that module's globals unit. A unit sees a segment's layout only if it uses a global of that module. Each thread reaches a segment through that segment's own thread-local pointer. |
| Global initialization | One function per module segment; the **program unit** calls them in the program's declaration order. |
| String and blob literals | External constants named by content digest, defined once in the program, in the literals unit of their digest shard. Equal literals therefore keep one address, which composite equality can observe (language spec §4.5). |
| Diagnostic locations | One table per instance, in the declaring module's locations unit. An abort site passes a pointer to its table entry. A line shift changes the locations unit and no code unit. |
| Nonlocal discriminant and channels | Defined once in the program unit and the target's unit; `extern` thread-local elsewhere. Target ids are a 31-bit digest of the target's `DeclKey`; a collision within a program is resolved deterministically and affects only the colliding targets. |
| Stack plan | Per-function constants relative to a hidden base, as today. Program totals appear only in the program unit. |
| `main`, exports, thread entries, runtime start | The program unit. |

The program unit is small and changes whenever the set of modules, the initialization order or the stack totals change.

### 17.5 Development and release

Optimization policy is independent of the semantic and numeric profile: `GS_DEBUG` selects checked arithmetic and conversions under any optimization policy.

| | Development | Release |
|---|---|---|
| Output | Units | Single file, as today; or units with link-time optimization if measurement favours it |
| Cross-unit inlining by the C compiler | None | Whole program |
| Goose inlining | As the selected `-O` level | As the selected `-O` level |
| Diagnostic locations | Table indirection | Inline constants |

Goose-level inlining copies a callee into its caller before emission, so an edit to an inlined helper changes every instance that inlined it and every unit holding one. That is a real dependency and is reported as such; the remedy in a development build is a lower Goose `-O` level, not hiding the dependency.

Link-time optimization is evaluated as a release-mode measurement only. It does not make units stable and does not reduce frontend cost.

### 17.6 Native compilation

The driver compiles changed units in parallel and may pass several units to one compiler process to amortize startup; batching invocations never merges units.

## 18. Fingerprints

| Fingerprint | Covers |
|---|---|
| `ContractDigest` | Goose compiler build identity; semantic profile; numeric profile; Goose `-O` level and optimization flags; target and ABI; runtime contract (`RuntimeVersion`); C compiler identity by binary digest and version; C flags; `-D` defines; stack reservation; evidence and checker versions. |
| `InputDigest` | Every file the compile read and every path it probed and found absent: sources, imports, package roots, sidecars, embedded files and shaders, `--include` headers; and the `ContractDigest`. |
| `ImplDigest` | The canonical lowered body (§16.2). |
| `UnitTextDigest` | The unit's exact text. |
| `ObjectKey` | `UnitTextDigest`, `ContractDigest`, and the digests of the non-toolchain headers the C compiler reports reading. |
| `LinkDigest` | The ordered object keys, the runtime object, native package link inputs and link flags. |

The existing runtime object key hashes the C compiler's path, not its binary (`src/toolchain.h:267`); `ContractDigest` uses the binary.

## 19. Reuse

Reuse is staged by boundary. A stage that is not reused is recomputed in full on every build, and the report says so.

| Boundary | Reused artifact | Key | Stage |
|---|---|---|---|
| Whole build | Everything | `InputDigest` | R0 |
| Native object | A unit's object | `ObjectKey` | R1 |
| Link | The executable | `LinkDigest` | R1 |
| Unit text | A unit's rendered C | Digest of its instances' pre-render form | R2, conditional |
| Checked result, Core, GIR, optimized body | Per context or implementation | Dependency sets (§19.4) | R3, deferred |

Object reuse under R1 is **not** incremental compilation of Goose: the frontend, the optimizer and emission run in full. It is called native-unit reuse everywhere.

### 19.1 R1: native-unit reuse

An object is a function of its unit's text, the headers the C compiler read, and the contract. The key contains all three, so no dependency of the object can be missing from the key, provided the C compiler is deterministic for fixed inputs. That proviso is an assumption, recorded in the trust ledger and tested by recompiling reused objects in verification mode (validation plan §10).

Because the key is content, R1 needs no dependency tracking above the unit text: whatever an edit changes, it either changes a unit's text or does not.

A link is skipped when `LinkDigest` matches the executable's recorded digest and the executable exists.

### 19.2 R0: no-op short-circuit

If `InputDigest` matches the last successful build's and its outputs exist, nothing runs. Completeness rests on every file read and every existence probe going through one recording reader; an unrecorded read is a defect class that the validation plan tests by construction (a reader that fails on any path not opened through it, enabled in the test suite).

### 19.3 Store

One directory per program build directory and `ContractDigest`. Within it: unit sources, objects named by unit key and text digest, and the link input list. A different contract uses a different directory; an entry from an incompatible store layout is in a directory the current compiler never reads.

| Event | Handling |
|---|---|
| Publish | Write to a temporary name in the same directory, then rename. An object is usable only once its completion record, holding its size and digest, has been written after the rename. |
| Interrupted write | An object without a completion record is absent; the next build recompiles and replaces it. |
| Corrupt entry | A size mismatch is detected on every use and a digest mismatch in verification mode; the entry is discarded and rebuilt, and the event is reported. |
| Missing store | A cold build. |
| Concurrent builds of one program | An advisory lock on the directory for the build's duration; the second build waits and then finds a warm store. |
| Disabled reuse | `--rebuild` ignores existing entries and replaces them. |
| Unreferenced objects | Deleted after a successful link. Other contracts' directories are left. |

Under R1 the frontend runs on every build, so diagnostics are always current. Under R0 the compiler does not run: the warnings of the last successful build are stored with its `InputDigest` and replayed, so a warm build prints what a cold one does. Their source locations are correct because the inputs are byte-identical. A failed build stores nothing, so an error is never replayed as a success and a previous executable is never reported as the result of a failing build.

### 19.4 R3: dependency sets (designed and shadow-tested here; reuse deferred)

Reusing a checked context without rechecking it requires knowing everything its result depended on.

| Dependency | Records |
|---|---|
| Body | The declaration's own token digest, excluding comments and positions. |
| Location | The declaration's positions, separately, so a line shift invalidates diagnostics and location tables only. |
| Interface | For each callee context: its signature, physical forms, result roots and normal-completion fact. |
| Inline | For each callee inlined: that callee's body dependency, transitively. |
| Layout | The layout digest of each `TypeKey` used. |
| Summary | The effect, return-root, store-record and nonlocal-target summaries read. For a recursive group, the group's fixpoint result and every member's body. |
| Lookup | For each name resolved or not found: the scope, the name and the digest of the candidate set. A new overload or import that adds a candidate invalidates the dependent even if the selected callee is unchanged. |
| Requests | The contexts this context requests. The live set is the closure from the entry points; an added or removed request changes membership and nothing else. |
| Resource | Embedded files and compile-time resources by content. |
| Diagnostic | The per-context warning verdicts. Consensus across a declaration's contexts is recomputed from verdicts on every build, so an added context can change a warning that no cached context produced. |

No dependency is a whole-program digest or an index into a whole-program table.

In this revision the compiler records these sets and **predicts** invalidation without acting on it. After each edit in the qualification matrix, the predicted-invalid set MUST contain every context whose recomputed result digest changed. A context that changed without being predicted is a defect in dependency recording, found before any checked result is ever reused. Reuse of checked results is deferred (campaign, deferral `X2`).

## 20. Cost report

`--build-report FILE` writes a versioned JSON report (`goose-build-report/1`). It is separate from the linter's facts and diagnostics and changes neither.

Counts, each distinct:

| Count | Meaning |
|---|---|
| Source functions | Declarations. |
| Checked contexts | Specializations created by the checker, including dead ones. |
| Entry-reachable contexts | Contexts reachable from entry points before optimization: the linter's `specialization_fanout` population. |
| Live instances | Contexts live after the optimizer's reachability. |
| Emitted instances | Bodies handed to emission, including element-run twins and thunks. |
| Implementations | Classes after sharing; and what the count would be with optimization off. |
| Inline expansions | Call sites inlined and nodes copied. |
| Helpers, types, data, runtime | Generated helpers by kind, type declarations, literals, runtime text: count and bytes each. |

Per source function: contexts, live instances, implementations, emitted bytes, node counts before and after optimization, nodes it contributed by being inlined elsewhere, and self check time.

Per specialization dimension and source function: the number of distinct values, and the number of contexts that would coincide if that dimension alone were ignored. This identifies whether growth comes from concrete types, roots, function values, captures, destinations, nonlocal targets or inlining.

Sharing: classes formed, and for instances that share a `DeclKey` and lowering key less consumed assumptions but not a body, the first differing dimension.

Phases: wall time, CPU time and peak resident memory for parse and resolve, check and specialize, optimize, bounds-check elimination, lowering, emission, each native compilation, link, and total. Under units: units written, units whose text changed, native compiler invocations, objects reused, whether the link ran, and for each changed unit the instances that changed it.

Timing and attribution cost nothing when the flag is absent.

## 21. Linter and bootstrap

Lint facts are built from the checked program before optimization and are unaffected by sharing, units and reuse. `specialization_fanout` continues to count checked, entry-reachable contexts. Emitted-code fanout, sharing, sizes and rebuild causes appear only in the cost report.

The bundled `goose-lint` is built from single-file C by the legacy pipeline. A units-built companion is compared against it by the existing linter suite as a qualification step, not as a build dependency. Ordinary `check` and `lint` run no backend work, compute no stable keys and need no Lean.

## 22. Closed decisions

| Question | Decision | Reopened by |
|---|---|---|
| Semantics style | One fuel-indexed interpreter per representation; no separate relational semantics. | A proof that needs intermediate states the interpreter cannot expose. |
| Nonlocal target | Static target set, innermost active activation. | A language change. |
| Reference lifetime on GIR | Established on Core, carried by the lowering theorem. | A GIR pass that creates references. |
| Serialization | Tagged JSON arrays, write-only in C++. | A second consumer that cannot parse them. |
| Stack plan | One stack per resizable slot. | Measured stack-count limits on a profile program. |
| Sharing criterion | Equality of canonical lowered bodies. | §16.5's measured gate. |
| Symbol identity | From `InstanceKey`, never from content. | — |
| Unit boundary | Declaring module and digest shard. | Measured churn or unit-count cost. |
| Native reuse key | Unit text, headers, contract. | A nondeterministic C compiler. |
| Checked-result reuse | Recorded and predicted, not acted on. | Deferral `X2`'s acceptance condition. |
| LLVM | Not part of this revision. | — |
