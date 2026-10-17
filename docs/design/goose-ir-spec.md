# Goose IR specification

**Schemas:** Goose Core 0.2, GIR-H 0.3, GIR-L 0.2. **Revision date:** 2026-10-12.
**Status:** Design contract for the [campaign](goose-ir-campaign.md). The C++ compiler implements `core-pilot`, flat fixed structs, and a checked subset of shrink operations through Core, GIR-H and native execution. The Lean Core model implements shrink-owner semantics with proved demand-aware safety for accepted Core modules. Whole-profile shrink lowering safety, complete source-to-native qualification, and construction remain pending. This specification does not claim their gates have passed.
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

The current implementation boundary is narrower than the full profile definitions above. Core 0.2, GIR-H 0.4 and GIR-L support the bounded flat fixed-struct slice with scalar fields as specified in §§12.4–12.5. The Lean Core model also implements shrink-owner semantics, while the demand-aware safety proof and GIR/native shrink path remain pending. Other `core-shrink` operations and all of `core-construction` remain prospective contracts.

Excluded from all three, each with its own feature id: references or slices stored in fields or elements (`stored-reference`), optionals, ADTs, relative references, pools and `reusable`, `varint`, floats, elementwise arithmetic, generics beyond what specialization already resolved, function values, threads, `extern fn`, serialization, declarations without initializers, temporaries viewed as slices, zero-size values.

Storing references only in variables, parameters and results is the single largest simplification: every root is exact, and no holder analysis is needed. Lifting it is a later profile.

## 3. Identities

Module-local dense ids: `StructId`, `FnId`, `VarId`, `TypeId`, `ScopeId`, `BlockId`, `ValueId`, `SlotId`, `OriginId`, and (construction profile) `TargetId`. They are deterministic for identical input and are never used across sessions. Cross-session identities are the stable keys of Part B (§15). Native addresses, hash-map iteration order and AST allocation order are never serialized.

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
        | varr Ty                        -- T[], default u32 length storage
```

`flat fixed` means built from `int`, `bool`, `arr` and `struct` only. Structs are nominal: distinct instantiated declarations remain distinct types even when their fields and layouts match. Their descriptors and field permissions are specified in §12.4. `grow` and `growshrink` types occur only as a variable type, a by-reference parameter's pointee, or (construction profile) a by-value parameter or result; neither can be stored as an array element or struct field. In `core-construction`, `varr` is also a recursively variable element type: it may occur inside `varr`, fixed `arr`, or `grow` elements, including fixed arrays whose own elements are variable. Such a fixed-count array is not flat fixed. Nonfixed struct fields, grow-shrink variable elements, limited variable elements, and stored references/slices remain excluded. The exact element restrictions of §12.8 and the recursive packed walk of §12.10 apply.

### 4.2 Values and memory

```text
RootInst ::= global VarId | local ActId ScopeInst VarId | staticBytes [Nat]
Obj      ::= scalar Val | fixed [Obj] | variable [Obj] | resizable [Obj]
           | limitedObj k [Obj] len | record StructId [Obj]
Loc      ::= (RootInst, [Nat])              -- root and selector path
Val      ::= int IntTy Int | bool Bool | unit | arrv [Val] | recv StructId [Val]
           | ref Loc | slice Loc start len | tuple [Val]
Store    ::= RootInst ⇀ Obj
```

`variable` is a completed `varr` object whose length never changes after construction. `staticBytes` is immutable literal storage and has no scope lifetime. Nonfixed objects are stored objects, never detached `Val` aggregates.

`ActId` is fresh for every call and `ScopeInst` for every block entry, including each loop iteration. Leaving a scope removes its root instances from the store. A `slice Loc start len` is a run of `len` elements of the array object at `Loc`. An access through a `Loc` whose root is absent or whose path is out of range is a **fault**, which is neither a Goose abort nor a rejection: it is the event the safety theorem proves unreachable for validated programs.

A `limitedObj` keeps every slot written so far; only `len` changes on `pop`. A reference to a popped slot stays valid and may read a later value of the same type. A `resizable` object's elements above its new length cease to exist on shrink.

Integers are mathematical integers with a range invariant for their type. Arithmetic is defined on `Int` followed by an explicit wrap; bitwise and shift operations are defined by conversion to and from a bit vector of the type's width. Signedness is part of the type.

### 4.3 Program structure

```text
Module  ::= schema, profile, numeric, sources, types, structs?, targets?, globals, impls, contexts, entry, origins
Impl    ::= name, params, results, vars, body, summary          -- executable; carries no roots
Context ::= impl ImplId, decl DeclKey, roots RootAnn             -- one checked specialization
Param   ::= VarId, Ty, mode (byValue | byRef)
RootAnn ::= var-roots (VarId ⇀ [RootRef]), result-roots [[RootRef]]
RootRef ::= var VarId | param Nat
```

`structs?` is absent in `core-pilot` and is the mandatory struct descriptor table in the flat-struct slice of `core-shrink` (§12.4). These optional fields in the abstract notation are selected by the profile, never inferred from record length. `core-construction` has both tables; `targets` names exact executable target sets (§7.2). Its result descriptors and concrete records are specified in §§12.8–12.9.

The split between **implementation** and **context** is deliberate. An implementation is everything execution needs. A context is one checked specialization of the source function: it points at an implementation and carries the root annotations the validator checks for that specialization. Several contexts may point at one implementation (§16), but every implementation has at least one context so its summary and roots are checked. Execution never reads a context.

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
        | push p e | pop p | ifE e b b | blockE b | arrLit [e] | arrFill e k
        | structLit StructId [e]             -- core-shrink, real fields in declaration order
Stmt  ::= let x e | assign p e | assignOp op p e | rebind x e | expr e | append p v
        | ifS e b b? | while e b | forRange x lo hi b | forEach x idx? v byRef b
        | ret e? | break | continue | print [PrintArg] | assert e | abort msg | exit e
        -- core-shrink
        | popN p e | resize p e fill? | clear p | assignWhole p e
Block ::= [Stmt] then optional value Expr
```

Reference transparency, overload selection, implicit conversions, member-call receivers and array-to-slice coercions are already resolved: Core records `read (deref …)`, the selected callee and each conversion explicitly.

### 4.5 Evaluation

The semantics is one total, fuel-indexed function

```text
eval : Fuel → NumericProfile → Module → Result
Result  ::= done Outcome Trace ConstructionTrace
          | timeout Trace ConstructionTrace | fault FaultKind
ConstructionTrace ::= [ConstructionEvent]    -- empty in earlier profiles
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
| `E-PUSH` | Resolve the owner once. For a fixed element, evaluate it before appending. For a nonfixed element, open its destination in the owner, construct it, then publish and yield its reference (§7.1). |
| `E-SHORT` | `and`/`or` evaluate the right side only when needed. |
| `E-RANGE` | `forRange` evaluates both bounds once. An empty or reversed range runs no iteration. |
| `E-EACH` | `forEach` over a resizable owner tests the current length before each iteration; over a slice, fixed or limited array it uses the length sampled at entry. |
| `E-SCOPE` | Leaving a block by fallthrough, `break`, `continue`, `ret` or propagation removes that block's roots. An abort removes nothing and ends the program. |
| `E-WHOLE` | `assignWhole p e` truncates `p` to empty, then builds `e` into it. |

`E-INDEX` and `E-LTR` were confirmed on the baseline compiler: `short[grow_and_index(short)]`, where the index expression pushes onto `short` and returns 1, prints the callee's output and then aborts with `index 1 out of bounds (length 1)`.

`print` writes its arguments' renderings and a newline: integers in decimal, booleans as `true`/`false`, literal text verbatim.

Abort kinds and the runtime text they correspond to: `div_zero` (`division by zero`), `div_overflow` (`integer overflow in division`), `index_oob` (`index I out of bounds (length N)`), `slice_oob` (`slice bounds out of range`), `assert`, `user_abort`; debug profile only: `int_overflow`, `cast_range`; `core-shrink`: `pop_empty`, `pop_n_range`, `resize_negative`, `resize_fill`, `capacity` (ordering and text in §12.6). An abort exits with status 1 after writing `goose runtime error: <text> (<file>:<line>)` to standard error.

### 4.6 Validation

`validate : Module → Except Rejection Unit` is independent of the C++ checker. It trusts no exported annotation: root annotations and effect summaries are checked, not assumed. It checks every **context** separately, including contexts that share an implementation. In-memory modules obey the same table constraints as decoded modules: every variable origin is in the origin table, every local variable's scope indexes the implementation's scope table, every implementation has a context, and each implementation or global initializer uses dense scope ids in block-opening order. The decoder checks that order while reading; validation checks it again for modules constructed directly.

| Rule | Check |
|---|---|
| `V-TYPE` | Every expression, place and statement is well typed; conversions are legal; arities match; each local variable's origin names an entry in the origin table. |
| `V-MUT` | Writes go through `mut` places; `let` variables are not reassigned; `rebind` targets a `var` of reference or slice type. |
| `V-ROOT` | A value with root set ρ may initialize, be assigned to, or rebind variable `r` only if ρ ⊆ roots(`r`) and every member of ρ outlives `r`. `param i` and globals outlive every local. A local `y` outlives `r` when `y`'s scope is `r`'s scope or an enclosing scope in the same implementation. Declaration order within one scope does not matter: a scope's variables all end together, and the language allows a `var` reference to be rebound to a later-declared variable of its own scope. A slice with root set ρ may be assigned through a reference parameter `p` to a slice variable only if ρ ⊆ content(`p`), the content roots the context declares for `p`; a slice read through `p` has the root set content(`p`). Content roots are declared only for a parameter of type `ref (slice T)`, whose root set is `[r_param p]`, and name only `r_param` and `r_global`. |
| `V-BLOCK` | The value of a block or `ifE` is not rooted at a variable declared inside it. |
| `V-RESULT` | A returned reference or slice is rooted only at `param i` or globals, within the declared result roots. |
| `V-CALL` | At a call, each `param i` in the callee context's result roots is replaced by the actual argument's roots; the argument's mutability satisfies the parameter's. A global's initializer is checked like a function body with no variables: nothing it reads, writes, grows or shrinks, itself or through its calls, may be a global that is not initialized before it. Where the callee context declares content roots for parameter `i`, its argument is a `var` slice variable `s` (`a_ref` of `p_local s`) or the pointee of a reference parameter `q` of the caller (`a_ref` of `p_deref(e_read(p_local q))`). Let κ be the callee's content roots with each `r_param j` replaced by argument `j`'s roots. For `s`: roots(`s`) ⊆ κ, κ ⊆ roots(`s`), and every member of κ outlives `s`. For `q`: κ and content(`q`) are the same set. So what the callee reads from the variable is within what it assumes, and what it stores there is within what the variable allows. |
| `V-SUMMARY` | Every target in `reads`, `writes`, `grows`, `shrinks` and `rebinds` names an existing parameter or global. Each implementation's effect summary is closed: the effects of its body, computed with its callees' summaries, are contained in it. Recursion needs no iteration, because closure is checked, not computed. The check runs once per context: a parameter target is read through that context's root annotation, so a parameter the context knows to be rooted at a global counts as that global. |
| `V-SHRINK` | At a possible shrink of a `grow` or `growshrink` owner, no demanded reference/slice variable, retained operand or loop run may point into its elements. References to its whole owner remain valid. Demand, possible aliasing and call substitution are defined in §12.6; reductions of a `limited` owner retain its written slots and require no such exclusion. |
| `V-WHOLE` | The right side of `assignWhole p e` neither names a variable rooted at `p`'s root nor calls an implementation whose summary reads, writes or resizes that root. |

`V-SHRINK` is at most as permissive as language spec §5.1. Where the frontend accepts a shrink through §5.1's `return`/`break` exception and the validator does not, the exporter reports `unsupported: shrink-exit-exception`.

An effect summary records, over the implementation's parameters and the globals: reads, element writes, growth, shrink, reference rebinding, possible abort, output, and the set of nonlocal targets it may propagate. Unknown is a distinct value that implies every effect.

The target of an effect is the set of global and parameter roots of the place reached; locals are not targets. The Lean validator's computation is the definition, and an exporter's summary must contain it:

| Effect | Arises from |
|---|---|
| reads | `read` of a place; every `viewOf`, wherever it occurs (sampling an owner reads its length), so also under `refOf (elem …)`, `sliceOf`, `lenOf`, `append` and `forEach`; the run an `append` copies from and the run a by-value `forEach` iterates, also when the run is a slice value; both sides of `assignOp`. |
| writes | `assign` and `assignOp` to a place. A slice assigned through a reference parameter is a write to that parameter's targets. |
| grows | `push` and `append` on the owner; `resize` with a fill; whole-resizable assignment. |
| shrinks | `pop`, `popN`, either form of `resize`, `clear` and whole-resizable assignment, including limited-array length reductions. A possible shrink is recorded even when the count is zero or a particular run grows instead. |
| rebinds | `rebind` of a variable that is a parameter. A slice assigned through a reference parameter `p` to the slice variable it refers to (`s_assign` to `p_deref(e_read(p_local p))`) is also a rebind of `param p`: one convention for replacing the slice a parameter's variable holds, whether the parameter is the slice or refers to it. |
| through a call | The callee's declared reads, writes, growth and shrink with each `param j` replaced by the targets of argument `j`'s roots. Where the callee context annotates parameter `j` with globals, those globals are added: the callee's own check lets an entry for `param j` stand for them, so the call must too. A callee whose summary is unknown makes the caller's unknown. |

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

Whole assignment is a shrink followed by construction (`E-WHOLE`, `V-WHOLE`). The exact executable S8 subset, memory transitions, abort order, validation and wire additions are in §12.6.

## 7. Construction and nonlocal exits (`core-construction`)

### 7.1 Construction

A nonfixed value exists only where the language's construction contexts provide storage (language spec §4.2). A destination is `(receiver storage and layout, logical result type, request, start, owner activation)`, with `request ::= value | element_run`. It denotes receiving storage, not a detached nonfixed value. `value` constructs one complete value including nested metadata; `element_run` constructs the elements of an array result and returns its count separately. `let`, parameters, whole assignment and `push` choose `value`; `append` of a nonfixed array producer chooses `element_run`. A fixed-array producer, including a fixed-array-returning call, is evaluated as an ordinary fixed value first and then its elements are appended; no result destination is passed into that call. Each nonfixed result position has its own destination. Calls, blocks and selected branches forward these destinations unchanged. Logical array result type and receiving array representation may differ only by the already-resolved array-family adaptation with identical element type. The destination retains the actual receiver layout; adapting outer metadata does not change its request kind or force an element-run specialization.

Receiver storage is resolved once before its constructing expression. A by-value nonfixed argument is built in a call-site region reserved for its parameter; the callee owns that parameter like a local. A result region belongs to the receiver, survives every callee's scope exit, and is never restored by an intermediate watermark. No nonfixed aggregate is an SSA value or a tuple element containing detached bytes. Core's logical objects describe the final bytes and metadata; destination state describes partial construction.

The separately compared construction trace is `begin(d)`, `write(d, index)`, `publish(d)`, `copy(src, d)`, `relocate(d, reason)`, `stage(d, reason)`, `abandon(d)`. A trace destination is numbered by dynamic `begin` order, including nested elements. `write` means completion of a logical element, not each native byte store. Internal writes are visible through the constructing value where allowed, but do not publish the containing receiver operation. `publish` makes that operation's complete value or element run live. A completed earlier `push` or `append` stays published; the initializers within one unfinished append literal are all part of its unpublished run.

| Rule | Statement |
|---|---|
| `C-ONCE` | Every initializer is evaluated exactly once, in source order; an exit or abort skips the remaining initializers. A fill evaluates its source once and copies that completed source for each repetition. |
| `C-DIRECT` | Delivering a fresh result to an unbounded resizable receiver introduces no `stage` or ordinary `copy`, including through calls, branches and multiple-result forwarding. Explicit copies of completed source storage and fill repetitions remain ordinary source operations, not a delivery fallback. Literal-byte initialization is a write, not an ordinary `copy`. |
| `C-RELOCATE` | `relocate` has exactly two reasons: `header-removal`, removing a packed value header and unused capacity in the same receiving storage to deliver elements to a run or a receiver with separate outer metadata, and `exit-value`, moving an exit's completed value down over abandoned construction in that same storage. Neither re-evaluates an initializer or changes logical reference targets. Variable-width prefix changes are outside these profiles (`varint`). |
| `C-STAGE` | `stage(d, capacity-check)` is permitted only for a limited receiver when the complete live result's size is unavailable before evaluation. The staged value is evaluated once, then checked and copied into free slots if it fits. A known size is checked before writing; an overflow never writes outside available slots. A capacity abort preserves preceding output. |
| `C-NOGROW` | While a nonfixed element destination in array `a` is open, no operation or transitive callee grows or shrinks `a`. Whole assignment also prohibits its right side from reading, writing or resizing its receiver (`V-WHOLE`). A pushed fixed element is evaluated before its destination opens and may grow its owner. |
| `C-NAMED` | Each nonfixed `value` result may nominate one local constructed at that result's destination from its declaration. All returns of that local are its last uses. Other returns preserve this alias only when their constructing values cannot read or write the local, directly or through aliases/callees; they use `C-ABANDON`. Returning a different local or a local reached by another return's value prevents the alias, and each taken return of a completed local emits one ordinary `copy`. Eligibility and its conservative boundary are specified in §12.8. An `element_run` specialization operating on a completed local uses the permitted callee-side copy; it does not claim value-form NRVO. |
| `C-ABANDON` | `return`, `return … from`, `break`, or `continue` that leaves a destination abandons exactly the unfinished destination portion it exits, once, including unfinished nested destinations. Completed earlier receiver operations and preceding output remain. The exit's own value is evaluated before abandonment can invalidate a source it needs; if built behind the discarded portion, it emits one `relocate(d, exit-value)` when moved down. No event is needed when no portion precedes it. |

Construction is not a transaction. Aborts and program `exit` terminate with the trace prefix already produced and do not run scope cleanup or manufacture publish/abandon events. Linear completion obligations apply to paths that resume or propagate a language return/break/continue, not to terminal abort/exit paths. A timeout may likewise end with open destinations.

### 7.2 Nonlocal return

`return E from f` returns the complete result list to the **innermost active call** whose implementation is a member of the statically resolved target set (language spec §7.9). Name and overload resolution happen in the returning function's definition environment. An unrelated function with the same leaf name cannot catch it. The checked legacy site has an exact `targetspec`; the exporter records its implementation as a singleton set. The table representation also permits a nonempty set of implementations with the same result types and destination requests. It never means all implementations sharing a printed name, nor an activation captured when a helper was declared.

```text
BodyResult ::= normal [Carrier] | returning [Carrier]
             | escaping TargetId [Carrier] | breaking | continuing
Carrier    ::= fixed Val | completed Destination
```

An activation saves its incoming destinations for each result position. A return site finds the nearest currently active member of its target and builds into those saved receiver channels; this lookup cannot use a destination from another activation of a recursive function. The result types and requests are the target's, not the helper's. Each intervening call propagates the same target and carriers. A member catches it, finishes `C-ABANDON`/`exit-value` landing, leaves its scopes, and returns normally to its caller; a nonmember leaves its scopes and propagates. The target's caller-owned destinations survive both paths.

Validation proves that every nonlocal target is active on every reachable call path to a return site. Recursive reuse cannot change the enclosing checked specialization; a missing active target is rejected, not a runtime fallback. Requirements and propagated targets are computed through calls and checked against summaries (§12.8). The recursion probe in the validation plan catches the deepest active `descend` and lets its outer activation resume.

Target ids index the executable target table, not the context table. Context erasure therefore preserves execution. Sharing renames each target's member set and MUST preserve membership: a quotient cannot merge a target member with a nonmember for any target, or merge target identities with different result protocols. Calls remain implementation-only. Function values remain excluded from these profiles; a later extension may translate their plain returns using the same mechanism.

## 8. GIR-H

### 8.1 Functions

A function has a signature, a slot table, a scope tree, a block table, an effect summary and an origin. A **slot** is memory-resident storage for one source variable: type, owning scope, and source `VarId`. Every source variable lowers to a slot; SSA values are temporaries. Promotion of slots to SSA is not part of this revision.

Blocks have typed parameters, an ordered instruction list and one terminator. Definitions dominate uses.

```text
VTy ::= int IntTy | bool | unit | ref Mut Ty | slice Mut Ty | view Ty | tuple [VTy]
      | dest Ty Request | built Ty Request   -- construction protocol only
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
| Shrink | `array.pop r`, `array.pop_n r n`, `array.resize r n fill?`, `array.clear r` | Pop yields the removed fixed element; the others yield unit. Ordering and aborts are §12.6. |
| Scopes | `scope.enter S`, `scope.leave S` | Slots of `S` are usable only between them. |
| Calls | `call f(args)` | Legal only when `f`'s summary propagates no nonlocal target. |
| Output | `print parts` | |
| Construction | `dest.open`, `dest.child`, `dest.write`, `dest.finish`, `dest.publish`, `dest.abandon`, `dest.copy`, `dest.relocate`, `dest.stage` | Linear destination and completion carriers, with call ownership transfer; exact signatures in §12.9. |

| Terminator | Contract |
|---|---|
| `br b(args)` | Arity and types match. |
| `condbr c, t(args), e(args)` | `c : bool`. |
| `ret vals` | Every scope of the function has been left. |
| `invoke f(args, destinations) normal b(results) escape [(target, block, results)]` | Required when `f` may propagate a nonlocal target; one typed escape edge per possible target (§12.9). |
| `escape target results` | Propagate the target-typed result carriers after leaving every scope of the function. |
| `abort kind origin` | Defined termination. |
| `exit v` | Program exit. |

`unreachable` is permitted only for a statically proven nonreturning call, with the concrete verifier rule of §12.2; it is never a substitute for an invoke escape edge.

### 8.3 Lowering from Core

Executable body lowering is a function of an implementation. GIR-H contains one function row per Core context, in context order. Each row carries that context's parameter, slice-content and result roots. Contexts sharing an implementation reuse its executable body without merging their root annotations.

Each Core rule maps to a fixed instruction sequence, so evaluation order is the instruction order: `E-INDEX` becomes `array.snapshot`, the index computation, `array.index.checked`; `E-ASSIGN` computes the destination reference before the right side. `forRange` puts its induction variable in a block parameter of the loop header, with the bound computed before the loop. A Core call to context `c` becomes a GIR-H call to function `c`. The entry retains its Core context index. Signatures are indexed by context as well. A context naming a missing implementation lowers to a function with no blocks, which the verifier rejects.

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
Fact ::= ge0 %i | lt %i %n | lenGe %r %n | viewLenGe %v %n
```

Generation, each with a soundness lemma in Lean:

| Rule | Premise | Fact |
|---|---|---|
| `F-CONST` | `%c = const i64 k`, `k ≥ 0` | `ge0 %c` |
| `F-CMP` | true edge of `condbr` on `int.cmp slt i64 %a %b` | `lt %a %b` |
| `F-LEN` | `%n = array.len %r` | `lenGe %r %n`, `ge0 %n` |
| `F-SNAP` | `%v = array.snapshot %r`, with `lenGe %r %n` | `viewLenGe %v %n` |

Kills: an instruction defining a value removes every fact that mentions it; entering a block removes facts about that block's parameters. A call, scope transition, initialization, store, push, append or shrink operation removes every `lenGe` fact. Facts are not substituted through block parameters in this first rule set; a later extension may add that rule with its proof.

`array.index.proven %v %i` requires `ge0 %i`, `lt %i %n` and `viewLenGe %v %n` for one `%n` at that instruction. The first rule set deliberately drops length facts at every mutation. Retaining them across grow-only push or append is a later rule and requires its own soundness proof.

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

The schema string names the representation and revision (`goose-core/0.2`, `gir-h/0.4`, `gir-l/0.2`). A reader accepts only the exact string it implements. Artifacts are not persisted across compiler versions, so there is no migration.

### 12.1 Tag table for goose-core/0.2

This subsection is the concrete encoding of §4 for profile `core-pilot`. A tag not listed here is `malformed` in that profile. The flat-struct slice of `core-shrink` extends it in §12.4 and the shrink slice in §12.6; construction extends the completed shrink profile in §12.8.

#### Lexical rules

A document is one module record followed by one line feed. The writer emits no whitespace except that line feed; the reader may accept any JSON whitespace. Strings are UTF-8; the writer escapes only `"` as `\"`, `\` as `\\` and the characters U+0000 to U+001F as `\u00xx` in lower-case hex, and writes everything else verbatim. Text that is not valid UTF-8 is `unsupported: non-utf8-text` in the exporter.

| Kind | Encoding |
|---|---|
| `nat` | JSON integer 0 to 2^31−1, no sign, no leading zero, no fraction or exponent. |
| `flag` | `nat` that is 0 or 1. |
| `str` | JSON string. |
| `int` | JSON string `-?(0|[1-9][0-9]*)` other than `-0`: a program integer constant. |
| `ty`, `var`, `glob`, `ctx`, `org`, `file`, `scope` | `nat`, an index into the type table, the current implementation's variable table, the global table, the context table, the origin table, the file table, or a scope number. |
| enumeration | A string from a closed set listed with the tag that uses it. |
| `[K]` | A bare JSON array, no tag, every element of kind `K`. It is not a record. |
| `[K]?` | A `[K]` of length 0 or 1: an optional `K`. |
| record | A JSON array whose first element is the tag string; the arity is the number of fields in the table, not counting the tag. |

Enumerations used below: `IntTy` is `i8 i16 i32 i64 u8 u16 u32 u64`; `Mut` is `mut const`; `VarKind` is `let var`; `Mode` is `by_value by_ref`; `UnOp` is `neg bitnot`; `BinOp` is `add sub mul div mod bitand bitor bitxor shl shr`; `CmpOp` is `eq ne lt le gt ge`; `ConvKind` is `widen as as_unchecked`.

#### Numbering

All ids are dense from 0 and fixed by the rules below, so the same program gives the same bytes. "Document order" is the order of bytes in the output.

| Table | Order |
|---|---|
| Contexts | The entry is context 0. Contexts are processed in id order; each `e_call` met in evaluation order whose callee context has no number yet takes the next. |
| Implementations | The exporter writes implementation `k` for context `k` and shares nothing. The `impl` field of a context exists so that a quotient (§16) can point several contexts at one implementation. |
| Globals | Program initialization order: imported modules first, then declaration order. Every global of the program is listed, used or not. |
| Variables of an implementation | Parameters first, in order; then each other variable in the document order of its declaring field: the `var` of `s_let`, `s_for_range`, `s_for_each` (element variable, then index variable). |
| Scopes of an implementation | One per `block` record, numbered in document order of the opening of the block; the body block is scope 0. |
| Types | Numbered by first mention in the document order of the globals, then the implementations (a type's components before the type); the contexts mention none. Equal types are one entry. A type's components therefore have smaller numbers. |
| Origins | Numbered by first mention in the same document order; equal `(file, line, kind)` triples are one entry. |
| Files | Numbered by first use in the origin table, in origin order. |

#### Module, tables and contexts

| Tag | Fields | Meaning |
|---|---|---|
| `module` | `str` schema (`goose-core/0.2`), `str` profile (`core-pilot`), `[file]` files, `[Ty]` types, `[global]` globals, `[impl]` impls, `[context]` contexts, `ctx` entry, `[origin]` origins | The numeric profile is not stored: it is a run parameter. The entry context has no parameters and no results. |
| `file` | `str` path | The path as the compiler writes it in runtime diagnostics. Conformance compares lines, not paths. |
| `origin` | `file`, `nat` line (from 1), `str` node kind | Node kind is one of `global param let assign assign_op rebind expr if while for return break continue print assert abort exit call index slice binary unary cast`. A synthesized operation takes the origin of the construct responsible for it (an array-to-slice coercion at a call argument takes the call's). |
| `global` | `str` name, `ty`, `VarKind`, `Expr` initializer, `org` | Initialized in global order before the entry runs. The initializer is read as a body with an empty variable table, so it names no local. |
| `impl` | `str` name, `[param]`, `[ty]` results, `[local]` variables, `block` body, `Summary` | Name is the source function's name for messages; it is not unique. Zero results is a unit result. |
| `param` | `var`, `Mode` | Parameter `i` is variable `i`, in scope 0. The mode is `by_ref` exactly when the variable's type is `ref`; the corresponding argument is `a_ref`. A free variable of a nested function is a trailing `by_ref` parameter. A captured slice variable is such a parameter of type `ref mut (slice M T)`; every root of the captured variable that is a local of an enclosing function must itself be passed as a parameter (captured or added as a further trailing `by_ref` parameter), so that the content roots below can name it. |
| `local` | `str` name, `ty`, `VarKind`, `scope`, `org` | One row per variable, including parameters (scope 0) and loop variables. `scope` is the block that declares it; a loop variable belongs to the loop's body block. |
| `context` | `impl` index (`nat`), `str` declaration key, `[vr]`, `[[RootRef]]` | One checked specialization. The declaration key is opaque to the Lean tool; the goldens write it as `module::name(written parameter types)`, and a byte comparison of exporter output with a golden ignores this field until stable keys exist. The `[vr]` list has one `vr` for each variable of the implementation whose type is `ref` or `slice`, in ascending variable order. The last field has one list per result. |
| `vr` | `var`, `[RootRef]`, optionally a second `[RootRef]` | Root set of that variable in this context. The optional third field is the **content roots** and is written exactly for a parameter whose type is `ref M (slice M' T)`; every other `vr` has two fields. For such a parameter `p` the root set is `[r_param p]` and the content roots list what the slice held in the variable `p` refers to may be rooted at, as the callee names it: `r_param j` for a root that is the caller's argument `j` (a caller local passed as parameter `j`), `r_global g` for a global; no `r_local`, and not `r_param p` itself. For a closure-converted captured slice variable these are the captured variable's own roots seen from the callee: each caller local among them as the `r_param` of the parameter it is passed as, each global as `r_global`. For a written `T[:]&` parameter they are the roots of the slice variable the context's caller passes, named the same way. At every call they must denote exactly the root set of the variable passed (`V-CALL`). |
| `r_local` | `var` | A local variable of this implementation. |
| `r_global` | `glob` | A global. The specialization knows a parameter's argument is rooted there. |
| `r_param` | `nat` index | Whatever the caller passed as parameter `i`: a caller local or an unconstrained root. |
| `summary` | `[Target]` reads, `[Target]` writes, `[Target]` grows, `[Target]` rebinds, `flag` aborts, `flag` outputs | Effect summary (§4.6) of the implementation, over its parameters and the globals. Target lists are sorted `t_param` by index, then `t_global` by index, without repeats. A target is in `reads`, `writes` or `grows` when the body, including callees mapped through the arguments, may read, store an element or scalar through, or push to the storage reachable from that parameter or global; `rebinds` when it may rebind a reference or slice variable that is that parameter. `aborts` is 1 when the body contains or calls `p_elem`, `e_slice`, `e_un` with `neg`, `e_bin` with `add sub mul div mod`, `e_conv` with `as`, `s_assert`, `s_abort` or `s_exit`; `outputs` is 1 when it contains or calls `s_print`. Locals are not targets. |
| `summary_unknown` | none | The distinct value that implies every effect. A summary field of an `impl` is `summary` or `summary_unknown`. |
| `t_param` | `nat` index | |
| `t_global` | `glob` | |

#### Types

| Tag | Fields | Meaning |
|---|---|---|
| `int` | `IntTy` | |
| `bool`, `unit` | none | |
| `arr` | `ty` element, `nat` count ≥ 1 | `T[k]` |
| `grow` | `ty` element | `T[>..]` |
| `ref` | `Mut`, `ty` pointee | `T&` or `const T&` The pointee may be a `slice` of a flat element type only as the type of a `by_ref` parameter; a reference to a reference, and a reference or slice inside an array or a global, remain outside the profile. |
| `slice` | `Mut`, `ty` element | `T[:]` |
| `tuple` | `[ty]`, length ≥ 2 | The type of a call with several results. No pilot form builds or takes one apart, so the exporter reports `unsupported: multiple-results`. |

#### Blocks and statements

Every statement ends with an `org` field.

| Tag | Fields | Meaning |
|---|---|---|
| `block` | `scope`, `[Stmt]`, `[Expr]?` value | A scope. Variables are declared by `s_let` or a loop statement inside it. The value is absent for a unit block. |
| `s_let` | `var`, `Expr`, `org` | Initialize a variable; `VarKind` is in its row. A `ref` or `slice` variable initialized from a reference expression is the `.=` form. |
| `s_assign` | `Place`, `Expr`, `org` | `E-ASSIGN` The place holds a flat value, or is `p_deref(e_read(p_local p))` for a parameter `p` that refers to a slice variable, which stores a slice through the reference (`V-ROOT`). A slice variable itself is changed by `s_rebind`. |
| `s_assign_op` | `BinOp`, `Place`, `Expr`, `org` | `E-ASSIGNOP` |
| `s_rebind` | `var`, `Expr`, `org` | Rebind a `var` of reference or slice type. |
| `s_expr` | `Expr`, `org` | Evaluate and discard. |
| `s_append` | `Place` grow-only owner, `View` source, `org` | |
| `s_if` | `Expr`, `block`, `[block]?` else, `org` | |
| `s_while` | `Expr`, `block`, `org` | |
| `s_for_range` | `var`, `Expr` lo, `Expr` hi, `block`, `org` | `E-RANGE`. The variable has the bounds' common integer type. |
| `s_for_each` | `var` element, `[var]?` index, `View`, `flag` by_ref, `block`, `org` | `E-EACH`. When `by_ref` is 1 the element variable has type `ref`. |
| `s_ret` | `[Expr]?`, `org` | |
| `s_break`, `s_continue` | `org` | |
| `s_print` | `[PrintArg]`, `org` | Writes the renderings, then a line feed. |
| `s_assert` | `Expr`, `org` | Abort `assert` when false. |
| `s_abort` | `str` message, `org` | Abort `user_abort`. |
| `s_exit` | `Expr`, `org` | |
| `pa_text` | `str` | Printed verbatim. |
| `pa_expr` | `Expr` | An integer (decimal) or boolean (`true`, `false`). |

#### Expressions, places, views, bounds, arguments

An expression, place or view that can abort or that is a call ends with an `org`; the others have none.

| Tag | Fields | Meaning |
|---|---|---|
| `e_lit` | `ty` (an integer type), `int` | The constant must lie in the type's range. |
| `e_bool` | `flag` | |
| `e_read` | `Place` | Read the value at the place. A reference variable read through transparency is `e_read(p_deref(e_read(p_local x)))`. |
| `e_ref` | `Mut`, `Place` | `refOf`. |
| `e_slice` | `Mut`, `View`, `Bound` lo, `Bound` hi, `org` | `E-SLICE`. Array-to-slice coercions are explicit. |
| `e_len` | `View` | The sampled length. |
| `e_un` | `UnOp`, `Expr`, `org` | |
| `e_bin` | `BinOp`, `Expr`, `Expr`, `org` | |
| `e_cmp` | `CmpOp`, `Expr`, `Expr` | |
| `e_and`, `e_or` | `Expr`, `Expr` | `E-SHORT` |
| `e_not` | `Expr` | Boolean not. |
| `e_conv` | `ConvKind`, `ty` target, `Expr`, `org` | |
| `e_call` | `ctx`, `[Arg]`, `org` | `E-CALL`. |
| `e_push` | `Place` grow-only owner, `Expr` | Yields a reference to the new element. |
| `e_if` | `Expr`, `block`, `block` | Both blocks yield a value. |
| `e_block` | `block` | |
| `e_arr` | `ty`, `[Expr]` | The result type is explicit: `arr` with exactly that many elements, or `grow` (possibly empty). |
| `e_fill` | `ty` (`arr`), `Expr` | Every element is the value, evaluated once. |
| `p_local` | `var` | A variable of this implementation. |
| `p_global` | `glob` | A global. |
| `p_deref` | `Expr` of `ref` type | The place it points to. For a parameter `p` of type `ref (slice T)` the only form is `p_deref(e_read(p_local p))`: the reference is dereferenced or passed on, never copied, returned or stored. |
| `p_elem` | `View`, `Expr` index, `org` | `E-INDEX`. |
| `v_of` | `Place` of `arr` or `grow` type | `viewOf`: the length is sampled now. |
| `v_val` | `Expr` of `slice` type | The slice's own run. |
| `b_expr` | `Expr` | |
| `b_end` | `Expr` | `fromEnd`: length minus the value. |
| `b_none` | none | `omitted`. |
| `a_val` | `Expr` | |
| `a_ref` | `Mut`, `Place` | Resolve the place and pass its reference. A slice-typed place is passed only as `p_local s` for a `var` slice variable `s` or as `p_deref(e_read(p_local q))`. |

A local or global reference is distinguished by tag (`p_local`, `p_global`, `r_local`, `r_global`, `t_global`). `p_field` is absent from `core-pilot`; the struct addition defines it in §12.4.

#### What the reader checks by tag and arity

Before type checking the decoder rejects: an unknown tag or enumeration value; a wrong arity or element kind; an index outside its table, with `var` checked against the current implementation's variable table (empty in a global initializer); a type whose components do not have smaller numbers; an `arr` count below 1; an `e_lit` whose `ty` is not an integer type or whose value is outside its range; a `param` that is not variable `i` at scope 0; a block whose `scope` is not the number of blocks opened before it in the implementation or global initializer; a `local` whose `scope` is not among the implementation's scopes; an unsorted or repeated target list or `vr` list; an `impl` or `context` index at or above its table size. Whether a variable's type, mode, roots or summary are right is the validator's work.

#### Expectation file

A golden `NAME.goose` has `NAME.core.json` and `NAME.out`, the standard output. `NAME.expect.json` is optional; without it the expectation is `["expect",["returned"]]`.

| Tag | Fields | Meaning |
|---|---|---|
| `expect` | `Outcome` | |
| `returned` | none | The entry returned. |
| `aborted` | abort kind, `nat` line | The abort kind is one of `div_zero div_overflow index_oob slice_oob assert user_abort int_overflow cast_range`; the line is that of the aborting operation's origin. |
| `exited` | `int` | `exit` was executed with that value. |

### 12.2 Tag table for gir-h/0.4

This subsection is the concrete encoding of §§8 and 10 for profile `core-pilot`, and the reference lowering of §8.3 whose output a conforming lowering reproduces byte for byte. A tag not listed here is `malformed` in that profile. The flat-struct slice of `core-shrink` extends it in §12.5 and the shrink slice in §12.6. Construction, `invoke` and `escape` extend the completed shrink profile in §12.9.

#### Lexical rules

The rules of §12.1 apply unchanged: one module record and one line feed, no other whitespace written, the same kinds `nat`, `flag`, `str`, `int`, `[K]`, `[K]?`, enumeration and record, the same string escapes. Table references add these kinds:

| Kind | Encoding |
|---|---|
| `ty` | `nat`, an index into the type table. A `ty` that must be a data type (everything except a block parameter's type) must not name a `view` entry. |
| `val` | `nat`, the id of an SSA value of the current function: a block parameter or the result of an instruction. Ids are dense from 0 within a function and each is defined once, in any order. |
| `slot`, `scope`, `block` | `nat`, an index into the current function's slot, scope or block table. |
| `fn`, `glob`, `org` | `nat`, an index into the function table, the global table, the origin table. |

Enumerations: those of §12.1 (`IntTy`, `Mut`, `VarKind`, `UnOp`, `BinOp`, `CmpOp`, `ConvKind`); `AbortKind` is `div_zero div_overflow index_oob slice_oob assert user_abort int_overflow cast_range`.

#### Numbering

The file table and the origin table are those of the Core module the lowering read, unchanged, so an abort names the same origin in both representations. Functions are the contexts of the Core module in order. Each row takes its executable body and unchanged summary from the implementation named by that context. Calls and entry retain context indices. The initializer of a global is the function held by its `global` record. Slots, scopes and globals have the numbers of the variables, blocks and globals of Core: slot `k` is variable `k`, scope `k` is the Core block numbered `k`. The remaining tables are numbered by these rules:

| Table | Order |
|---|---|
| Types | By first mention in document order of the globals, then the functions (each function: parameters, results, slots, then its blocks' parameters and instructions, left to right within a record); a type's components before the type. Equal types are one entry, so a type's components have smaller numbers. The file and origin tables mention none. |
| Blocks of a function | In order of creation by the reference lowering, below. Block 0 is the entry. |
| Values of a function | In order of creation by the reference lowering: a block's parameters when the block is created, an instruction's result when the instruction is emitted. The numbers need not follow definition order in the output. |
| Scopes of a function | The parent of scope `k` is the Core block that encloses block `k`; the body of an implementation is scope 0 with no parent. A global initializer has no body scope: each block its expression contains is a root, so several scopes have no parent. A scope that only dead code opens is still in the table. |

#### Module, functions and tables

| Tag | Fields | Meaning |
|---|---|---|
| `module` | `str` schema (`gir-h/0.4`), `str` profile (`core-pilot`), `[file]` files, `[Ty]` types, `[global]` globals, `[func]` funcs, `fn` entry, `[origin]` origins | `file` and `origin` are as in §12.1. The entry function has no parameters and no results. |
| `global` | `str` name, `ty`, `VarKind`, `func` init, `org` | The initializer is a function with no parameters whose one result has the global's type; it is run in global order, in a fresh activation, before the entry. Its summary is `summary_unknown` and its origin is the global's. |
| `func` | `str` name, `[ty]` params, `[ty]` results, `[slot]`, `[scope]`, `[block]`, `roots`, `Summary`, `[org]?` origin, `[certificate]?` | Block 0 is the entry and its parameters have the types `params`. `roots` carries conservative parameter, slice-content and result roots from this function's Core context alone, using parameter positions and the function's slot and global numbers. The verifier checks that the body and call sites fit these annotations before using them to check effects. The summary is the one of the Core implementation, unchanged, and is checked against the body (§9, `GIR-V050`). The origin of an implementation is that of its first variable, absent when it has none. The optional certificate has one fact set per block and is required exactly when the function contains `i_index_proven`. |
| `slot` | `ty`, `VarKind`, `scope` owner, `nat` var | Memory-resident storage of the source variable `var`. Its address is a `ref` that is `mut` exactly when the kind is `var`. |
| `scope` | `[scope]?` parent | A parent has a smaller number. |
| `block` | `[bp]` params, `[inst]` | One terminator is required, last. Zero or several are decoded and rejected by the verifier. |
| `bp` | `val`, `ty` | A block parameter. |
| `summary`, `summary_unknown`, `t_param`, `t_global` | as in §12.1 | Target indices are against this function's parameters and the globals. |
| `roots` | `[vr]`, `[cr]`, `[[RootRef]]` | Parameter roots, slice-content roots for `ref slice` parameters, and one root set per result. |
| `vr`, `cr` | `nat` parameter position, `[RootRef]` | A row in parameter roots or content roots. A root is `r_local slot`, `r_global glob`, or `r_param` parameter position. |

Types are the Core types (`int bool unit arr grow ref slice tuple`, fields as in §12.1) and one more:

| Tag | Fields | Meaning |
|---|---|---|
| `view` | `Mut`, `ty` element | A sampled run of elements of an array or slice: region, start and length. It is an SSA value only, and the element is a data type. |

#### Instructions

Each instruction record that defines a value begins with that value's `val`. The result type follows from the operand types and is not written, except where the table gives one.

| Tag | Fields after the result | Result type, and what it does |
|---|---|---|
| `i_int` | `ty` integer, `int` | The constant, in range. |
| `i_bool` | `flag` | `bool` |
| `i_unit` | none | `unit` |
| `i_bin` | `BinOp`, `ty` integer, `val` a, `val` b, `[org]?` | `T` (the stated type; both operands have it). `add sub mul div mod` can abort and need an origin. |
| `i_un` | `UnOp`, `ty` integer, `val`, `[org]?` | `T`. `neg` can abort, needs an origin and is not applied to an unsigned type. |
| `i_cmp` | `CmpOp`, `ty` integer, `val` a, `val` b | `bool` |
| `i_bcmp` | `CmpOp` (`eq` or `ne`), `val` a, `val` b | `bool`; both operands are `bool`. |
| `i_not` | `val` | `bool`; the operand is `bool`. |
| `i_conv` | `ConvKind`, `ty` source, `ty` target, `val`, `[org]?` | The target integer type. `as` can abort and needs an origin; `widen` must preserve every value. |
| `i_next` | `ty` integer, `val` | `T`. The operand plus one, used for a loop counter. It is total: it does not fault at the type's maximum, because Core's model lets a counter pass it (a run longer than the counter type's range), and the lowering theorem needs the two to agree at every fuel. The checker rejects such index types in source programs. |
| `i_slot` | `slot` | `ref M T` for the slot's type `T` and `M` from its kind. |
| `i_global` | `glob` | `ref M T` likewise. |
| `i_elem` | `val` view, `val` index | `ref M T` for a view `view M T`. The address of element `index` of the run: no check and no read, so an index outside the object faults when the address is used. |
| `i_freeze` | `val` ref | `ref const T`, the same address. |
| `i_load` | `val` ref | `T` for `ref M T`. `T` is flat, a reference or a slice. |
| `i_snap` | `SnapshotMode`, `val` ref to `arr` or `grow` | `view M E`: region and current length sampled now. `owner` keeps the array element mutability even when the binding is immutable; `borrowed` inherits the reference mutability. |
| `i_sview` | `val` slice | `view M E`: the slice's own run. |
| `i_vlen` | `val` view | `i64`, the sampled length. |
| `i_vslice` | `Mut`, `val` view, `Bound` lo, `Bound` hi, `[org]?` | `slice M E`. Aborts `slice_oob` unless `0 ≤ lo ≤ hi ≤ length`, where an omitted `lo` is 0 and an omitted `hi` the length, and `bd_end` is the length minus the value, computed on mathematical integers. Needs an origin. |
| `i_alen` | `val` ref to `arr` or `grow` | `i64`, the length now. |
| `i_index` | `val` view, `val` index, `[org]?` | `ref M E`. Aborts `index_oob` unless `0 ≤ index < length`, the length being the view's. Needs an origin. |
| `i_index_proven` | `val` view, `val` index | `ref M E`. The fact certificate proves `0 ≤ index < length`; execution performs no bounds branch and this instruction needs no origin. |
| `i_push` | `val` ref to `grow`, `val` element, `[org]?` | `ref mut E`, to the new element. |
| `i_call` | `fn`, `[val]` args, `[org]?` | The callee's result type, `unit` for no result. Each argument must be accepted by its parameter (a `mut` reference or slice may stand for a `const` one). Needs an origin. |
| `i_arr` | `ty` (`arr` with that many elements, or `grow`), `[val]` | The array value; the elements have the element type. |
| `i_fill` | `ty` (`arr`), `val` | The array whose every element is the value. |
| `x_init` | `slot`, `val`, `[org]?` | Brings the slot's storage into existence holding the value, which has the slot's type. The slot's scope is entered. Needs an origin. |
| `x_store` | `val` ref, `val`, `[org]?` | Stores the value at a `mut` reference to a flat, reference or slice type; the value has the pointee type. Needs an origin. |
| `x_append` | `val` ref to `grow`, `val` view, `[org]?` | Appends the elements of the view's run to the array, copied before any is written. Needs an origin. |
| `x_enter`, `x_leave` | `scope` | Enters, leaves a scope. |
| `x_print` | `[PrintPart]`, `[org]?` | Writes the renderings, then a line feed. Needs an origin. |
| `pp_text`, `pp_val` | `str`; `val` (an integer or a boolean) | A print part. |
| `bd_none`, `bd_val`, `bd_end` | none; `val`; `val` (an integer of any type) | A bound of `i_vslice`. |

| Terminator | Fields | Meaning |
|---|---|---|
| `t_br` | `block`, `[val]` | Arity and types equal the target's parameters. |
| `t_condbr` | `val` (`bool`), `block`, `[val]`, `block`, `[val]` | True edge first. |
| `t_ret` | `[val]`, `[org]?` | The values have the function's result types. |
| `t_abort` | `AbortKind`, `[org]?` | Needs an origin. |
| `t_exit` | `val` (an integer), `[org]?` | Needs an origin. |
| `t_unreachable` | none | The previous instruction is a call to a context proven not to return. Reaching this terminator faults with `flow`. |

A non-aborting operation may carry an origin that the table does not require.

#### Evidence records

The optional function field is `[]` for no certificate and `[["certificate", BlockFacts]]` when present. `BlockFacts` is a list in block order; each entry is a list of the facts asserted at that block's entry. The writer sorts and removes duplicate facts. The checker rejects duplicates, ill-typed facts, a nonempty entry set, a block-count mismatch, a fact not implied by every predecessor, and an unjustified `i_index_proven`.

| Tag | Fields | Meaning |
|---|---|---|
| `f_ge0` | `val` integer | `ge0` |
| `f_lt` | `val` integer, `val` integer | `lt` |
| `f_len_ge` | `val` reference, `val` integer | `lenGe` |
| `f_view_len_ge` | `val` view, `val` integer | `viewLenGe` |

#### What the reader checks by tag and arity

Before verification the decoder rejects: an unknown tag or enumeration value; a wrong arity or element kind; a `ty`, `slot`, `scope`, `block`, `fn`, `glob` or `org` outside its table (a `val` only has to be below 2^31); a type whose components do not have smaller numbers, a `view` used as a component, an `arr` count below 1; an `i_int` whose type is not an integer type or whose value is outside its range; a scope whose parent is not an earlier scope; a type that is not an integer type where one is required; an unsorted or repeated summary target list or one naming a parameter or global that does not exist; trailing data, input over 64 MiB, nesting deeper than 256, more than `2^24` instructions in one function. The schema and profile strings must be exactly `gir-h/0.4` and `core-pilot`. Everything else is the verifier's.

#### What the verifier checks for this profile

The checks run in the order of their codes over the whole module, so a module is reported under the first code at which any function fails.

| Code | Pilot checks |
|---|---|
| `GIR-V001` | Entry exists and takes and returns nothing; each global's initializer takes nothing and returns the global's type; every table index and origin in range; each function has a block; scope parents earlier; each value defined once with ids dense from 0; summary targets exist. |
| `GIR-V010` | Block 0's parameters are the function's parameters; slot types are storable; every instruction's operands have the types its row requires; `x_init`, `x_store` and `x_append` types; `t_condbr`, `t_ret` and `t_exit` operands. |
| `GIR-V020` | Exactly one terminator per block, last; edge arguments match the target's parameters in number and type; the entry has no predecessor; every block is reachable; every use is dominated by its definition (a use in the same block follows it); `t_unreachable` immediately follows a call to a function whose body proves it has no normal return path. The proof starts with every function possibly returning and removes only bodies with no reachable `t_ret`, treating a reached `t_unreachable` as unknown. |
| `GIR-V030` | `i_slot` and `x_init` only while the slot's scope is entered; `x_store`, `i_push` and `x_append` only through a `mut` reference; `i_load` and `x_store` only of a flat, reference or slice type. |
| `GIR-V040` | `x_enter` only when the scope's parent is the innermost entered scope (or it has none and none is entered); `x_leave` only of the innermost; every path to a block enters the same scopes; `t_ret` with none entered. |
| `GIR-V050` | The summary closes over the effects of the body (below). |
| `GIR-V080` | Every certificate has the shape and typing above; replay of §10's rules implies every block-entry fact and justifies every `i_index_proven`. |
| `GIR-V100` | Every operation marked "needs an origin" has one. |

The body determines reference provenance and result roots. Every reference, slice or view value gets the set of roots it may have: `i_slot` gives its slot (a local), `i_global` its global, the entry block's parameter `i` the parameter `i`; `i_elem`, `i_freeze`, `i_snap`, `i_sview`, `i_vslice`, `i_index`, `i_index_proven` and `i_push` keep the roots of their operand; `i_load` of a reference or slice gives the union of what was stored in the slots of its operand's roots and the declared content roots when loading through a `ref slice` parameter; a block parameter gets what its incoming edges pass; a call gives its callee's body-derived returned roots with each `param j` replaced by the roots of argument `j`. A slot holds the union of what `x_init` and `x_store` put in it. Result roots are the least fixed point over function bodies and recursive calls. The `roots` record is a conservative annotation: computed result roots must be included, parameter roots must cover the roots supplied at each call, and content roots must cover the backing roots passed at each call. The verifier checks these bounds before using annotations to check effects, so missing annotations cannot hide an effect. Reads are `i_load`, `i_snap` and `i_alen` through a reference; writes are `x_store`; grows are `i_push` and `x_append`; each is attributed to the parameter and global roots of its operand and to nothing for a local. A store through the slot of a reference-typed parameter rebinds that parameter. Aborting is `i_bin` with `add sub mul div mod`, `i_un` with `neg`, `i_conv` with `as`, `i_vslice`, `i_index`, `t_abort` and `t_exit`; `i_index_proven` is non-aborting. Printing is `x_print`. A call adds its callee's summary with parameters mapped through the argument roots and the globals listed in those parameter root annotations; a callee with an unknown summary makes this function's own summary unknown unless it is already. Each effect must be in the summary.

Before comparing storage effects with a known summary, the Lean verifier expands parameter targets on both sides through the function's checked parameter root annotations. Absent or empty annotations retain the generic parameter root. Reads, writes, grows and shrinks use this expansion. Rebinds name parameter bindings and retain their parameter indices.

#### The reference lowering

A conforming lowering makes the same choices. The lowering emits into one current block. `newBlock(T…)` takes the next block id and then the next value ids, one per parameter type. An instruction that defines a value takes the next value id when it is emitted. A terminator closes the current block and leaves none. While no block is current nothing is emitted, no block is created, and statements are skipped, so there is no unreachable block and no instruction after a terminator. Joins are created only when some path reaches them. In the lists below a name in `⟦…⟧` means "the lowering of", values are named by the order their operands are lowered, and `[org]` is the Core node's origin.

Expressions:

| Core | Lowering |
|---|---|
| `e_lit`, `e_bool` | `i_int` `i_bool` |
| `e_read p` | `⟦p⟧`, `i_load` |
| `e_ref m p` | `⟦p⟧`; `i_freeze` only if `m` is `const` and the address is `mut` |
| `e_slice m v lo hi` | `⟦v⟧`; `lo` (`⟦e⟧` then `bd_val`, `bd_end` for `b_end`, `bd_none`); `hi`; `i_vslice m` `[org]` |
| `e_len v` | `⟦v⟧`, `i_vlen` |
| `e_un`, `e_bin` | operands left to right; `i_un` or `i_bin` with the first operand's type and `[org]` |
| `e_cmp` | operands; `i_cmp` with the first operand's type, `i_bcmp` for booleans |
| `e_and a b` | `⟦a⟧` as `x`; create block `R` then block `J(bool)`; `t_condbr x R [] J [x]`; in `R`: `⟦b⟧` as `y`, `t_br J [y]`; continue in `J`, whose parameter is the result. `e_or` is `t_condbr x J [x] R []`. |
| `e_not` | `i_not` |
| `e_conv` | operand; `i_conv` with the operand's type and the target `[org]` |
| `e_call c` | arguments left to right (`a_val e`: `⟦e⟧`; `a_ref m p`: `⟦p⟧`, frozen as in `e_ref`); `i_call` of the implementation context `c` names, `[org]` |
| `e_push p e` | `⟦p⟧`, `⟦e⟧`, `i_push` with no origin |
| `e_if c t f` | `⟦c⟧`; create `T` then `E`; `t_condbr`; lower the then block in `T` and the else block in `E` (with a unit constant for a block with no value); if some arm still has a current block, create `J(τ)` with `τ` the type of the first such arm's value and append `t_br J [v]` to each arm that has one; continue in `J` |
| `e_block b` | the block, below |
| `e_arr`, `e_fill` | elements or value; `i_arr`, `i_fill` |
| `p_local x`, `p_global g` | `i_slot x`, `i_global g` |
| `p_deref e` | `⟦e⟧`, no instruction |
| `p_elem v i` | `⟦v⟧`, `⟦i⟧`, `i_index` `[org]` |
| `v_of p` | `⟦p⟧`, `i_snap` |
| `v_val e` | `⟦e⟧`, `i_sview` |

A block: `x_enter` of its scope; the variables its construct declares are bound with `x_init` (a function's parameters in order, a range loop's counter, a `for` loop's element then index); the statements; the value, or a unit constant when one is wanted and absent; `x_leave`. A function body is lowered into block 0 after creating it with the parameters' types, and when the body falls through it ends with `t_ret [v]` (or `t_ret []` for no result) and no origin. A result-bearing body with no tail value must diverge under Core validation. If such a body leaves a synthetic live frontier (for example, the false edge of `while true`), after its scope leaves the lowering branches to a fresh zero-parameter sink that branches to itself, with no return or origin. This rule applies only when the body's divergence check succeeds; other finalization retains the return form above.

Statements:

| Core | Lowering |
|---|---|
| `s_let x e` | `⟦e⟧`, `x_init x` `[org]` |
| `s_assign p e` | `⟦p⟧`, `⟦e⟧`, `x_store` `[org]` |
| `s_assign_op op p e` | `⟦p⟧`, `i_load`, `⟦e⟧`, `i_bin op` `[org]`, `x_store` `[org]` |
| `s_rebind x e` | `⟦e⟧`, `i_slot x`, `x_store` `[org]` |
| `s_expr e` | `⟦e⟧` |
| `s_append p v` | `⟦p⟧`, `⟦v⟧`, `x_append` `[org]` |
| `s_if c t` | `⟦c⟧`; create `T` then `J`; `t_condbr c T [] J []`; the block in `T`; `t_br J []`; continue in `J`. With an else block: create `T` then `E`; `t_condbr`; both arms; the join `J` is created afterwards, only if an arm still has a current block, and each such arm gets `t_br J []`. |
| `s_while c b` | create `H`; `t_br H []`; in `H`: `⟦c⟧`, create `B` then `X`, `t_condbr c B [] X []`; the body in `B` with a `continue` that branches to `H`; `t_br H []`; continue in `X` |
| `s_for_range x lo hi b` | `⟦lo⟧` as `a`, `⟦hi⟧` as `n`; create `H(T)` with `T` the type of `a`, parameter `i`; `t_br H [a]`; in `H`: `i_cmp lt T i n`, create `B` then `X`, `t_condbr`; the body in `B` with `x_init x i` after its `x_enter`; at its end, and at each `continue` after leaving the loop's scopes, `i_next T i` then `t_br H [next]`; continue in `X` |
| `s_for_each x j v by_ref b` | the source once: `v_of p`: `⟦p⟧` as `r`, `i_snap r` as `w`; `v_val e`: `⟦e⟧`, `i_sview` as `w`. Unless `r`'s pointee is `grow`: `i_vlen w` as `n`. Then `i_int i64 0`; create `H(i64)`, parameter `i`; `t_br H [zero]`; in `H`: for a `grow` source `i_alen r` as `n`; `i_cmp lt i64 i n`; create `B` then `X`; `t_condbr`; in `B`, before the body's scope: `i_elem w i` as `e`, then the element value: `i_load e`, or for `by_ref` the address (`i_freeze` if the loop variable's type is a `const` reference); the body with `x_init x` of that value and then `x_init j i` for an index variable; the increment and `continue` as for a range loop with type `i64`; continue in `X` |
| `s_ret [e]` | `⟦e⟧`; `x_leave` of every entered scope, innermost first; `t_ret [v]` `[org]` |
| `s_break`, `s_continue` | `x_leave` of the scopes entered since the loop began, innermost first; `t_br X []`, or the loop's continue step |
| `s_print` | the `pa_expr` arguments' `⟦e⟧` in order; one `x_print` `[org]` with the parts in order |
| `s_assert e` | `⟦e⟧`; create `P` then `F`; `t_condbr c P [] F []`; in `F`: `t_abort assert` `[org]`; continue in `P` |
| `s_abort` | `t_abort user_abort` `[org]`; the message is not kept |
| `s_exit e` | `⟦e⟧`, `t_exit` `[org]` |

A global's initializer is a function with no parameters whose block 0 holds `⟦e⟧` and `t_ret [v]` with the global's origin. Every origin an instruction carries is the Core node's own; the prologue's `x_init` of a parameter carries the parameter variable's origin; `i_next`, `i_push`, `i_freeze`, the loop constants, `x_enter`, `x_leave`, `t_br` and `t_condbr` carry none.

### 12.3 Tag table for gir-l/0.2

The low stage (§11) in the same style: tagged arrays, no objects, decimal integers for every table reference, one module record and one line feed. It is written by the compiler (`--emit-gir-low`) and no reader exists, so there are no decoder rules; the compiler's own verifier (`GIR-V090`, with the checks of §9 that apply) judges the module in memory before it is written. Types are `int`, `bool`, `unit` as in §12.1 and one more, `ptr`, an address. Every value of the low stage is an integer, a boolean or an address; an array by value is the address of its bytes.

| Tag | Fields | Meaning |
|---|---|---|
| `module` | `str` schema (`gir-l/0.2`), `str` profile, `[file]`, `[Ty]`, `[lglobal]`, `[lfunc]`, `fn` entry, `[fn]` initializers, `nat` stacks, `nat` global stacks, `[origin]` | `file` and `origin` as in §12.1. The initializers run in order before the entry. The program starts with `stacks` data stacks and `global stacks` more for resizable globals. |
| `lglobal` | `str` name, `scalar` `ty` \| `bytes` `nat` size \| `header` | A global's storage: a scalar, a block of bytes, or a resizable's header (its elements are on a stack of its own). |
| `lfunc` | `str` name, `[ty]` params, `[ty]` results, `nat` stacks, `[member]`, `[nat]` scope parents (`-1` for none), `[block]` | Parameter 0 is the base of the function's data stacks (`i64`). An array or multi-value result is written through an address passed as parameter 1. At most one scalar result. The function owns stacks `0..stacks-1` above its base. |
| `m_scalar`, `m_bytes`, `m_header` | `ty` \| `nat` size \| `nat` stack, `nat` scope, `str` name | A member of the frame: a scalar variable, a block of bytes, or a header `{base, len}` whose elements are on stack `stack`. The scope bounds its life. |
| `block`, `bp` | as in §12.2 | The same CFG. |

Shared with §12.2, over integers, booleans and addresses (`i_int`, `i_bool`, `i_cmp`, `i_not`, `i_conv`, `i_call`, `t_br`, `t_condbr`, `t_ret`, `t_exit`), with these differences: `i_bin` and `i_un` carry a `flag` before their origin that is 1 where the operation is the runtime's checked one (`add sub mul div mod`, `neg`) and 0 where it wraps or is bitwise; `i_cmp` may have type `bool`; `i_call` has result `-1` when the callee has none, and its first argument is the stack base; `t_abort` is `["t_abort", AbortKind, [val], [org]?, str]` with the operands of the message (`index_oob`: the index and the length) and the text of a user abort.

| Tag | Fields after the result | Meaning |
|---|---|---|
| `l_offset` | `val` address, `val` i64 index, `nat` element size | `address + index * size`. |
| `l_load`, `l_store` | `ty`, `val` address (, `val`) | Load or store of a scalar or address. |
| `l_frame` | `nat` member | The address of a frame member. |
| `l_get`, `l_set` | `nat` member (, `val`) | Read or write a scalar member. |
| `l_stack` | `val` base, `nat` offset | The data stack `base + offset`. |
| `l_mark`, `l_release`, `l_bump` | `val` stack (, `val` mark) \| `val` stack, `val` bytes or `-1`, `nat` bytes | The stack's top; restoring it (only on a stack the function owns, or a passed resizable owner in `core-shrink`, §12.6); moving it up. |
| `l_gaddr`, `l_gstack` | `nat` global | A global's storage and its stack. |
| `l_hbase`, `l_hlen`, `l_hinit`, `l_hsetlen` | `val` header (, `val`) | A header's base and length; setting its base with length 0; setting its length. |
| `l_copy`, `l_move`, `l_fill` | `val` dst, `val` src, (`nat` element size,) `val` count | Bytes copied (regions do not overlap), moved (they may), or a source of `size` bytes repeated `count` times. |
| `l_rt` | `str` entry point, `val` argument or `-1`, `str` text | A call of the closed list `out_int out_uint out_bool out_text out_nl`, which write the argument, the text, or a line feed. |

Every check of §8 is a compare and a conditional branch to a block that ends in `t_abort`; no view, scope, snapshot, slot or checked index remains.

### 12.4 Flat fixed structs in goose-core/0.2, core-shrink

This is the integrated first `S8` extension: flat fixed structs are supported through C++ Core export, GIR-H, GIR-L and native execution. This slice does not include the owner shrink operations in §12.6 or establish `G-SHRINK`. The `core-pilot` module still has exactly nine fields after its tag, has no struct table, and accepts none of the tags added here. Its writer's numbering, tags and bytes are unchanged. A reader selects the module shape from the schema and profile strings before decoding its tables; it does not try both arities. All lexical limits of §12.1 apply.

#### Module and nominal identity

| Tag | Fields | Meaning |
|---|---|---|
| `module` | `str` schema (`goose-core/0.2`), `str` profile (`core-shrink`), `[file]` files, `[Ty]` types, `[struct_def]` structs, `[global]` globals, `[impl]` impls, `[context]` contexts, `ctx` entry, `[origin]` origins | Exactly ten fields after the tag. The mandatory structs table follows types, including when it is empty. Other records keep their pilot shape except the profile-selected shrink additions in §12.6. |
| `struct` | `sid` | A type entry naming one descriptor in this module's structs table. |
| `struct_def` | `nat` byte size, `[field]` real fields | One instantiated nominal struct declaration, with positive byte size. Pads may supply that size without real fields; zero-size values remain excluded. |
| `field` | `ty` type, `VarKind` binding, `Mut` contents, `nat` byte offset | Binding `var` permits assignment of the whole field; binding `let` does not. Contents `const` forbid writes inside the field; contents `mut` permit them subject to enclosing storage permissions. |

`sid` is a JSON `nat` indexing the structs table. There is one descriptor per instantiated nominal declaration; two declarations with equal field types, permissions and layout still have different ids. Distinct generic instantiations are distinct nominal types. No declaration key, AST address or physical layout is used as structural equality of nominal types. An implementation may store the descriptor's resolved field types with its nominal id internally; the wire type remains `struct sid`.

The exporter reserves a struct id at the first mention of its instantiated type in the existing type traversal, then visits its real fields in declaration order to intern their component types before interning the containing `struct` type. Thus struct ids need not follow the order of the corresponding type entries. Every descriptor has exactly one corresponding `struct` type entry. All field type indices are smaller than that containing type index, including nested struct and array types; this excludes recursive by-value nesting. Existing component-before-parent type numbering is preserved. Fields have no names on the wire: selection has already been resolved.

Real fields are numbered densely from zero in declaration order. A `pad n` or bare `pad` declaration has no logical field index, no initializer, and no value in the record. The exporter maps the checked frontend field indices, which also enumerate pads, to these real-field indices. The byte gaps left by pads are retained in layout metadata. No selector can refer to padding.

#### Layout and permissions

The descriptor's byte size and field offsets come from the existing packed layout of the instantiated frontend field run (`StructInst`, `FieldRun`, and the `StructLayout`/`LayoutFields` calculation). The exporter and GIR placement use that same calculation. They must not introduce a second rule for packing, bare-pad alignment or tail padding. Logical Core memory uses field indices; byte offsets are placement metadata, not logical selectors.

The decoder checks descriptor arities, closed enumerations, table indices, positive size and the earlier-component rule. `V-TYPE` additionally requires flat fixed field types, increasing nonoverlapping field extents, and every field extent within the declared byte size, with checked size arithmetic. Gaps and trailing pad bytes are allowed; a zero-size field, stored reference or slice, variable field or resizable field is outside this slice. Layout metadata is validated for bounds independently of the source exporter; equivalence to the frontend's packed layout is checked by conformance, not asserted by a Lean proof about logical memory.

Binding and contents permissions are independent. `let inner: S` has binding `let` and contents `mut`; `const inner: S` has binding `let` and contents `const`; `outer: const S` has binding `var` and contents `const`. A scalar's contents permission is still recorded, although assigning that scalar is governed by its binding permission. Copies produce independent value snapshots; declaration-level field permissions remain in force in the copy.

Place checking therefore distinguishes permission to replace the whole place from permission to mutate its contents. An unqualified local or global owns mutable contents even when its binding is `let`. For `p_field p j`, whole-field assignment requires writable contents of `p` and binding `var` of field `j`; writes inside that field require writable contents of `p` and contents `mut` of field `j`. A read-only reference forbids both. The same rule propagates through nested fields and fixed-array elements. The permissions come from declarations and reference types, not from the value currently stored there. Root identity, lifetime and read/write summary targets remain those of the containing place.

#### Construction, selection and evaluation

| Tag | Fields | Meaning |
|---|---|---|
| `e_struct` | `ty` struct type, `[Expr]` initializers | Exactly one expression per real field, in declaration order; each expression has the declared field type. |
| `p_field` | `Place` containing storage, `nat` real-field index | A place holding that field of a nominal struct. The index is checked against its descriptor. No origin is needed: selection has no defined Goose abort. |

An `e_struct` evaluates its initializers exactly once, left to right, and produces `recv sid [values]`. A checked literal includes the explicit or synthesized default initializer for every real field; the reader does not evaluate defaults or infer omitted fields. Binding `let` and contents `const` constrain later writes, not initialization. An abort or exit in an initializer ends evaluation immediately and preserves the already-produced trace. A flat record does not require the nonfixed destination protocol of §7.

`p_field` evaluates its containing place once and appends the real-field index to its logical location path. Reading yields a value snapshot; writing rebuilds only the selected subvalue, preserving nominal identity and sibling fields. A record is distinct from an array: field storage traversal does not make the record itself a view, expose a length or permit indexing it as an array. An unvalidated wrong shape or invalid selector may fault; `V-TYPE` must make these faults unreachable for validated programs. This does not add a new runtime abort or change the numeric profile.

The first executable slice is scalar-field struct locals with construction, field read/write, copying and printing the scalar fields. Whole-object `const` qualification, including `const` struct locals, parameters and results, is explicitly `unsupported: struct-whole-const` until its type encoding and copy rules are added. A field's contents permission is already represented by the descriptor. Forming or passing a reference to an aggregate field whose effective whole-binding and contents capabilities differ is outside this first executable slice: plain `ref Mut T` cannot retain both. The Core validator rejects that reference formation; direct field/element selection still retains both capabilities. The later field-reference extension must preserve split provenance as required by §12.5, rather than keeping this conservative rejection as its final contract. Projection from a temporary or returned value such as `make().field` or `S { ... }.field` is `unsupported: struct-temporary-projection` until an expression projection or a specified storage materialization is added; `p_field` never accepts an expression in place of its `Place`. Other flat-struct contexts not implemented by that slice remain `unsupported: struct`; this contract does not claim complete flat-struct support or `G-SHRINK`.

### 12.5 Flat fixed structs in gir-h/0.4, core-shrink

This extension is relative to the `gir-h/0.4` pilot schema of §12.2. It leaves that schema's `core-pilot` module arity of eight fields after the tag, numbering and bytes unchanged. The profile selects the additional table explicitly.

| Tag | Fields | Meaning |
|---|---|---|
| `module` | `str` schema (`gir-h/0.4`), `str` profile (`core-shrink`), `[file]` files, `[Ty]` types, `[struct_def]` structs, `[global]` globals, `[func]` funcs, `fn` entry, `[origin]` origins | Exactly nine fields after the tag. |
| `struct`, `struct_def`, `field` | as in §12.4 | GIR-H retains nominal identity, logical field order, field permissions and authoritative layout. A descriptor's `ty` fields refer to the GIR-H type table and never to a `view`. |
| `i_struct` | `val` result, `ty` struct type, `[val]` initializers | A transient by-value record. Operand count and types match the real fields. |
| `i_field` | `val` result, `val` containing reference, `nat` real-field index | A reference to the selected field; no read, write, check, origin or runtime abort. |

Core lowering retains struct ids and descriptor order, remapping their type references into GIR-H's component-before-parent type table. `e_struct` lowers each initializer in declaration order, then emits `i_struct`. `p_field` lowers its containing place once, then emits `i_field`. Record slots and globals, `i_load`, `x_init`, `x_store`, by-value arguments and results retain the nominal struct type and snapshot behavior.

`GIR-V010` checks nominal type identity, flat field types, selector bounds and constructor operand arity/types. `GIR-V030` checks whole-store and contents permissions separately, including the writable contents of an unqualified `let` owner. An address's contents capability follows its owner provenance through `i_slot`, `i_global` and field/element projection; it must not be inferred from binding kind alone. A read-only reference parameter or `i_freeze` supplies no writable contents capability. A whole-field reference can be read-only for whole-store purposes while still permitting a further projection into mutable contents of an owned `let` field. The verifier must establish this distinction from provenance and descriptor permissions; an arbitrary `ref const S` is not upgraded. Scope and summary checks retain the containing root, and no instruction escapes the checks by substituting a structurally equal nominal type.

GIR-L (§12.3) has no struct type, descriptor table, constructor or field operation after lowering. A flat record lives in byte storage, its by-value load takes a byte snapshot, and a field reference becomes address arithmetic using the descriptor's byte offset. Only the existing low scalar, address and byte-copy operations remain. Padding is not a logical value and must never become an operand of scalar output or field access. Whole-object equality, when implemented, compares real fields and ignores padding.

The C emitter must support unaligned packed scalar accesses. A low `PLoad` or `PStore` that may address an unaligned field copies bytes between that address and a scalar temporary using the existing copy primitive or `memcpy`; it must not cast the address to an aligned scalar pointer and dereference it. The storage layout remains the frontend's authoritative packed layout.

### 12.6 Shrink operations in core-shrink

The Lean Core model implements the shrink-owner semantics in this contract, including permission and transitive-effect checks. `validated_steps_keep_invariant` and `validated_never_faults` prove demand-aware safety for accepted Core modules, including `core-shrink`. These theorems do not establish GIR lowering safety or complete source-to-native qualification. No shrink gate is claimed complete. This contract extends §§12.4–12.5 at schemas `goose-core/0.2`, `gir-h/0.4` and `gir-l/0.2`. A schema/profile pair selects one shape; no decoder tries alternate arities. `core-pilot` retains every tag, module/summary arity, numbering and byte choice in §§12.1–12.3. The `core-shrink` Core module has ten fields after its tag and GIR-H has nine, including the mandatory struct table even when empty. Flat-struct types, descriptors and field operations retain §§12.4–12.5's shapes. The completed shrink profile changes its summary and `e_push` shapes as specified below; a pre-shrink flat-struct artifact using their pilot shapes is malformed under this contract.

#### Supported types, storage and source boundary

| Core/GIR-H type tag | Fields (arity after tag) | Contract |
|---|---|---|
| `growshrink` | `ty` element (1) | `T[>..<]`; flat fixed element type. |
| `limited` | `ty` element, `nat` capacity (2) | `T[..k]`, `1 ≤ k ≤ 2^31−1`; flat fixed element type. |

Their component type precedes the containing type. Here flat fixed elements are precisely §4.1's integers, booleans, fixed arrays and nominal flat structs: neither references/slices nor limited arrays occur inside an element. The slice supports `grow`, `growshrink` and `limited` as owned local/global arrays and as the pointee of a by-reference parameter. References to their whole owner, element references, slices, indexing, `.len`, `push`, `append`, iteration and the operations below work subject to their ordinary permission/root rules. It adds neither resizable fields nor dynamic-capacity `T[..]`. A `limited` is fixed-class in Goose, but this slice supports it only as an owner: by-value limited parameters/results, aggregate embedding, whole-object copies and whole limited-array assignment are `unsupported: limited-value`; they are not silently treated as clear-then-construct. Runtime-capacity arrays remain `unsupported: runtime-capacity`. By-value resizable arguments/results, `copy` of a nonfixed owner and nonfixed-result calls remain outside S8 (`unsupported: nonfixed-construction`). These are support boundaries, not changes to the source rules of language spec §3.4, §4.4 and §5.3.

The exporter rejects the following source forms before publishing any Core/GIR artifact; a support failure includes its source location and is never represented by an opaque tag or a partially emitted module. The existing pilot/flat-struct exclusions also remain in force.

| Excluded source form in this slice | Export feature id |
|---|---|
| Runtime-capacity `T[..]`, including `[..cap]` construction | `runtime-capacity` |
| Static limited capacity zero, or greater than the wire `nat` limit | `zero-size`, or `capacity-limit`, respectively |
| Limited initializer whose branches/block values are not literal runs (including array/slice variables, `copy`, `default` and limited-result calls) | `limited-initializer` |
| `.cap`/`cap(owner)` on a limited owner | `limited-capacity` |
| An owner fill literal `[value;count]` | `owner-fill-literal` |
| By-value limited arguments/results, limited aggregate embedding/copy or whole limited-array assignment | `limited-value` |
| By-value resizable arguments/results, nonfixed `copy`/result calls, or a grow/growshrink initializer/replacement with a nonliteral-run leaf | `nonfixed-construction` |
| Resizable tail fields or a value containing a resizable tail | `resizable-field` |
| Reference/slice/nonfixed/limited element types of a new owner | `nonflat-element` |
| `.index_of`/`index_of(owner,ref)` | `builtin-call` |

A fresh owner initializer is `e_arr` of its exact owner type, possibly chosen by `e_if` or `e_block`; each leaf is a literal run of flat fixed elements. A `limited` leaf has at most its capacity elements (`V-TYPE` rejects a forged larger literal). `e_fill` remains the fixed-array form; an owner fill literal `[value;count]` is `unsupported: owner-fill-literal` until a count-bearing owner-run form is specified. Repeating the expression in `e_arr` would violate evaluation-once, and global initializers have no local-variable table for a synthesized fill temporary. Empty owner literals are legal. A direct `s_expr(e_arr …)` may evaluate a fresh owner literal run and discard it. Otherwise an owner cannot be read as a first-class value by `e_read`/`i_load`: the transient run cannot escape, initialize any other destination, or be stored or copied. Its only storage consumers are owner initialization and the whole-resizable replacement below. No destination capability or first-class owner copy is added.

`e_push` in `core-shrink` has fields `Place`, `Expr`, `org` (arity 3); its pilot form has arity 2. Resolve the owner, evaluate the element once, then read the current length and, for a limited owner, check capacity before any receiver write. It returns `ref mut E` to the written slot. This origin supplies a limited-capacity abort's source location. `s_append` keeps fields `Place`, `View`, `org` (arity 3), extending its owner type to the three supported kinds. Its source run is sampled and copied before receiver writes; the limited capacity check uses the receiver length after source evaluation and precedes every receiver write. A self-append keeps its sampled source intact. All count/size arithmetic used for checks is mathematical, with checked physical byte-size arithmetic at placement.

#### Core operation tags and evaluation order

| Tag | Fields (arity after tag) | Type and behavior |
|---|---|---|
| `e_pop` | `Place` owner, `org` (2) | Result `E`, a fixed value snapshot of the last element. Resolve the owner once, read current length, check nonempty, copy its last value, then reduce the length by one. A discarded pop is `s_expr(e_pop …)`, never a separate `s_pop`. |
| `s_pop_n` | `Place` owner, `Expr` count, `org` (3) | Resolve owner, evaluate count once, then read current length; check `0 ≤ count ≤ len`, then reduce by count. Result unit. |
| `s_resize` | `Place` owner, `Expr` size, `[Expr]?` fill, `org` (4) | Resolve owner; evaluate size once, then, only if size evaluation completed normally, the present fill once, even on a shrink, unchanged length or later size-check abort; only then read current length and check. Fill has type `E`. |
| `s_clear` | `Place` owner, `org` (2) | Resolve owner once, then reduce length to zero. No defined abort of its own. |
| `s_assign_whole` | `Place` owner, `Expr` replacement, `org` (3) | Only `grow`/`growshrink`. Resolve owner, clear its old elements, then evaluate and publish its replacement literal run once. Replacement has the exact owner type; `V-WHOLE` applies before any evaluation. |

The first four operate on all three kinds. Element mutation requires writable contents; changing an owner's length also requires writable contents. Direct whole replacement of a named owner requires a `var` binding: `s_assign_whole` of a `let` local/global is rejected by `V-MUT`, even when its contents are writable. For a whole `grow`/`growshrink` owner, however, forming or passing `ref mut` uses the owner's writable contents permission, so a `let` binding does not prevent that borrow. A callee receiving `ref mut (grow E)` or `ref mut (growshrink E)` may replace the referenced owner through its parameter, subject to `V-SHRINK` and `V-WHOLE`, including when the caller passed a writable-contents `let` owner. This permission is specific to borrowing a whole resizable owner; it does not upgrade scalar or struct binding permissions, read-only contents, or an arbitrary `ref const`. Whole limited-array assignment remains unsupported. Source `.resize(n)` and `.resize(n,v)` map to an empty/singleton fill option, never a default fill. The count or size expression may itself grow or shrink the same owner; the outer operation uses the length these effects leave. The receiver location, not its length, is retained across those operands. Pop returns the old last value, not a reference to released storage. `E-WHOLE` is clear-before-RHS, including when an RHS effect aborts; whole limited-array assignment has different source semantics and is outside this slice.

The size operand is an integer of any supported width. In accordance with the legacy runtime check, its value is interpreted as an `i64` bit pattern for the negative-size check: a `u64` above `i64.max` aborts `resize_negative`, rather than allocating an enormous region or using a debug `as` check. Every smaller nonnegative value keeps its mathematical value. Pop counts use their mathematical integer value, so any negative count or count exceeding length aborts `pop_n_range` without signed conversion.

#### Kept slots, truncation and aborts

For `limitedObj k slots len`, `slots.length` is the number of slots ever written in this root instance, and `0 ≤ len ≤ slots.length ≤ k`. It is a high-water extent, distinct from visible length. Reducing length changes only `len`: `pop`, `pop_n`, resize-down and clear preserve every slot and its value. A retained location into index `j < slots.length` and any field/fixed-array selector inside it stays valid even if `j ≥ len`. A fresh index or slice still checks the visible sampled length, and can never expose a never-written slot. Push/resize-up/append overwrite the slots starting at `len` and extend the high-water extent only where needed. Retained references then read the newly written value. Owner scope exit invalidates all its locations as usual.

For `resizable slots`, length is `slots.length`. A reduction truncates that vector: a location into a removed element becomes invalid and does not become valid merely because later growth reuses its index. The live-location theorem must prohibit observing that dead reference; it cannot use index reuse as evidence that the old lifetime survived. Owner/header references remain valid across either reduction. `pop` copies its result before truncation. Fresh initialization and whole-resizable replacement create only fully initialized element values; limited unused capacity has no logical values and is not zero-filled.

Resize checks, in order after its operands, are: (1) negative interpreted size; (2) if size exceeds current length and fill is absent, `resize_fill`; (3) if growing a limited owner with fill and size exceeds capacity, `capacity`. Equal length does nothing after evaluating fill. A lower size truncates/preserves slots as above; a higher size copies the single evaluated fill into each added slot and then publishes the new length. Pop checks empty before copying; pop_n checks its range before any length/slot mutation. Capacity checks in push and append happen after operand effects and before receiver writes. An abort does not roll back output or mutations made while resolving the owner/evaluating operands; “before mutation” describes this operation's subsequent receiver mutation. No check is debug-only.

| Abort kind | Runtime text | Runtime error id |
|---|---|---|
| `pop_empty` | `pop on empty array` | `GS_E_POP` |
| `pop_n_range` | `pop_n count negative or beyond the array's length` | `GS_E_POPN` |
| `resize_negative` | `resize to a negative length` | `GS_E_RESIZENEG` |
| `resize_fill` | `resize growth requires a fill value` | `GS_E_RESIZEFILL` |
| `capacity` | `limited array capacity exceeded` | `GS_E_CAPACITY` |

Each uses the operation's origin and §4.5's status/stderr boundary. These five kinds extend `AbortKind` in Core expectation files, GIR-H `t_abort` and GIR-L `t_abort` only for `core-shrink`; the decoder rejects them under `core-pilot`. Their GIR-L message-operand list is empty. A malformed type/arity is a decoder failure; a well-decoded lifetime or permission violation is validation rejection; an unchecked access to removed/unwritten storage is a model fault, never one of these Goose aborts.

#### Summary shape and shrink targets

`summary` under `core-shrink` has exactly seven fields: `[Target]` reads, `[Target]` writes, `[Target]` grows, **`[Target]` shrinks**, `[Target]` rebinds, `flag` aborts, `flag` outputs. The target representation, order and duplicate checks remain §12.1's. `summary_unknown` keeps arity zero. This shape applies to both Core implementations and GIR-H functions. Six fields are malformed under this profile; seven are malformed under `core-pilot`. Adding a shrink list to an internal summary must not change its pilot serialization.

Each shrink operation reads its owner's length and has a shrink effect on that owner's parameter/global targets; the local owner itself is not a summary target. `pop` also reads the removed element. Resize with fill also writes elements and grows, conservatively even if it never grows in one execution. No-fill resize cannot successfully grow: it contributes reads, shrinks and possible abort, but no own element-write or growth effect. Push/append write added elements and grow; limited push/append must set `aborts = 1` for capacity checks. Both `V-SUMMARY` and `GIR-V050` reject a summary omitting that abort flag, even when a literal/constant count would fit; receiver/operand effects are included separately. Whole replacement reads the owner's length and shrinks, writes and grows its targets, as well as including RHS effects. Pop, pop_n and resize may abort; clear has no own abort. Every operation also includes the effects of its places/operands. A limited reduction is a summary shrink because its visible length changes, although it invalidates no slot; bounds facts depending on length are still killed.

At a call, map every callee shrink target through the same checked argument roots and parameter-global annotations used for reads/writes/grows in `V-CALL`/`V-SUMMARY`. Include effects of captured variables, which are ordinary trailing by-reference parameters. Unknown implies reads/writes/grows/shrinks of every reachable owner and possible abort/output; it cannot discharge a shrink safety check. Summaries conservatively cover possible successful effects and possible aborts, using the operation classes above without count-constant narrowing, optimization or execution. Thus fill-resize is always marked growing, no-fill resize never is, and every resize is marked shrinking. An abort flag describes a possible check, not a receiver mutation on its failure path. `V-SUMMARY` checks closure across all contexts and recursive calls without trusting a partially computed recursive summary.

#### Demand-sensitive V-SHRINK

Demand is source-syntactic future use, computed over the unoptimized structured Core separately for each context, before checking a shrink. Expand variable mentions in explicit closure-converted arguments and root/content annotations; a call that uses a captured variable thus counts as a mention. Distinguish an owner/header reference from an interior reference or slice. A flat fixed value snapshot contains no roots and cannot become a live alias merely because it was read from the owner.

For a point inside an expression, the demand set includes variables named in every later operand, in the enclosing statement's remaining evaluations, in the block value and later statements of each enclosing block. Take unions at conditionals, including both branches even if a condition is constant. Leaving an inner block drops its locals from continuation demand but retains outer variables mentioned later. A completed statement does not demand a variable solely because its binding remains in scope. At declarations/rebindings retain syntactic later mentions; do not subtract a future definition as if it established a new lifetime. Thus last-use-before-shrink is accepted outside loops, but a shrink before a later rebind and use can be conservatively rejected. This is not optimizer liveness.

Within a loop, add all outer variables mentioned anywhere in its condition/body and the demand after the loop; forRange bounds and forEach sources are evaluated once and are handled before entry, not reevaluated on the backedge. Body locals participate only while their own scope instance is entered. Computing unions to a fixed point over loop backedges gives the same enclosing-loop demand at every iteration; no finite unrolling is a proof. `break`, `continue` and `ret` still include syntactic enclosing continuations for this profile. The language's return/break exception, balanced-call recognition and more precise rebind analysis are not encoded: when they are needed for a frontend-accepted program, export reports `unsupported: shrink-exit-exception`, `unsupported: shrink-balanced-call` or `unsupported: shrink-demand`, respectively.

The validator derives a demand set for every evaluation point as checked internal proof metadata; no new wire annotation is trusted or serialized. The canonical evaluation-step invariant and its exported preservation theorem must refer to those demand sets together with the active evaluation frames/runs. In particular, the Core step specifications' `StoreInv.live` and `Frame.vis` obligations must become demand-aware, and their exported step theorem must use that revised invariant. They must not quantify validity over every reference bit in the store or every variable visible in a scope: dead reference values may remain stored after truncation, provided no later permitted evaluation observes them. The store still meets value/type-shape invariants, and active limited slots retain their type-valid values. Extending a pilot invariant that required all stored references to be valid without this demand restriction would reject legitimate last-use-before-shrink programs.

Variable demand is only one part of the invariant. An evaluation frame retains earlier reference/slice operands until their consuming operation completes: an assignment destination, earlier call argument, sampled indexing/slicing run, append source run, and iteration run of a slice/fixed/limited owner. Such a retained value is checked at every later shrink even if its source variable has no later mention. A scalar/flat record already loaded by value is not retained as a reference. A by-value iteration over a grow/growshrink owner retains the owner/header, rereads length each iteration and copies its element before running the body; that copied element alone does not prevent shrinking. A by-reference element binding participates in demand, and any retained slice iteration run prevents a resizable shrink for the duration of the loop.

For each demanded variable or retained value, obtain its checked roots (and the pointee slice's content roots for a `ref slice` parameter). It can conflict only if its type/provenance may reach an element of the shrinking owner; the whole-owner reference used to shrink is not itself a conflict. Two distinct local roots, two distinct global roots, and a local root versus a global root are distinct. Abstract `r_param` identities do not establish distinctness from another compatible parameter or global. Use existing concrete root/context evidence when it establishes distinctness; otherwise compatible abstract roots may overlap. No alias annotation is added. If this conservative overlap alone prevents exporting a frontend-accepted program, report `unsupported: shrink-parameter-alias`. Calling a shrink function with one owner twice never gets a disjointness assumption from its two parameter positions.

Check direct operations at the actual mutation point (after count/fill evaluation); count/fill effects receive their own checks with all retained operands. At a call, also apply its substituted may-shrink summary against caller continuation demand and caller retained values. Conservatively retain reference/slice actual arguments across a call that may shrink, except whole-owner arguments: this can require `unsupported: shrink-demand` when only a more precise callee operand lifetime would admit it. Callee contexts must independently pass their own demand checks. Globals whose references are demanded by a call count through their roots; the profile does not permit stored/global references into grow-shrink arrays. Unknown calls cannot bypass either side. Rejection uses validation's shrink reason and offending variable/value, never a runtime abort.

`V-WHOLE` additionally checks all replacement operands and called summaries for any possible use of the cleared owner, its elements or an alias: reads, writes, grows, shrinks and rebinding that can reach it are forbidden. This includes the evaluation of closure-converted captured arguments and every branch/block, not just the path executed. Fixed sibling-field accesses are allowed only where existing concrete place/type evidence proves they cannot reach the owner. The fresh literal-run forms below make this restriction independently checkable without S9's destination protocol.

#### GIR-H tags, reference lowering and verifier obligations

| Tag | Fields after tag (including result where present) | Meaning |
|---|---|---|
| `i_pop` | `val` result, `val` owner reference, `[org]?` (3) | Fixed result `E`; pop check/copy/reduce in Core order. Origin required. |
| `x_pop_n` | `val` owner reference, `val` integer count, `[org]?` (3) | Checked count reduction. Origin required. |
| `x_resize` | `val` owner reference, `val` integer size, `[val]?` fill, `[org]?` (4) | Optional fill exactly `E`; checks and transition above. Origin required. |
| `x_clear` | `val` owner reference, `[org]?` (2) | Reduce to zero. Origin required for reference lowering and diagnostics. |
| `x_replace` | `val` owner reference, `val` fresh owner run, `[org]?` (3) | Only grow/growshrink of exactly the same element/owner type; publish a replacement into an owner proven empty. Origin required. |

Inherited `i_snap`, `i_alen`, `i_push` and `x_append` accept the additional owner kinds with the unchanged GIR-H arities. `i_arr` accepts `growshrink` and `limited` literal-run result types; limited literal count is checked against capacity. No `load`/`store` of an owner, implicit array-kind conversion or nonfixed call is introduced.

Reference lowering resolves the place once, lowers count then fill in order, then emits the respective operation. `e_pop` emits `i_pop`; `s_pop_n`, `s_resize`, `s_clear` emit their `x_` forms. Every emitted operation carries `[org]` from its Core node. `s_assign_whole` emits `x_clear` before lowering its RHS and then `x_replace`. Even an RHS that aborts/terminates sees the old owner already cleared; no replacement is emitted on that path. `e_arr` lowers elements left to right and then `i_arr`; `e_if`/`e_block` use the existing block/value lowering. No artificial slot is added merely to turn the transient run into an append view.

`x_replace` accepts only a value defined by `i_arr` of the exact grow/growshrink type, or a block parameter whose every reachable incoming value recursively has that literal-run provenance. This is the least fixed point seeded by `i_arr`; an unseeded cycle, a call result, a load, an arbitrary function argument and a limited value do not qualify. Its operand evaluations must not use the receiver's may-alias roots. The verifier derives these dependencies from values, slots, calls and CFG paths, not a writer flag. Before replacement, every path must have established that receiver's emptiness by `x_clear`, with no intervening possible growth/replacement of an alias. A forward must-fact records empty receivers, intersects at joins with edge substitution, and kills emptiness on growth/replacement/unknown calls affecting any may-alias owner. Different parameter ids cannot preserve an emptiness fact across an aliased growth. The originating clear and replacement therefore cannot be detached by a forged CFG. Replacement does not itself clear; clear is the explicit shrink effect.

`GIR-V010` checks owner kinds, exact element/result/fill types and literal counts; `GIR-V020` covers SSA/control flow as before. `GIR-V030` checks contents permissions for every length/element mutation and the replacement permission just defined: direct replacement of a `let` owner is rejected, while replacement through a mutable whole-resizable reference parameter is permitted even when its checked caller roots name a writable-contents `let` owner. Whole-owner borrow formation and lowering must preserve that contents permission independently of the caller binding kind; this is no scalar/struct permission upgrade. `GIR-V040` checks owner scope availability. `GIR-V050` derives and closes over reads/writes/grows/**shrinks**, recursive callees and conservative roots before trusting a summary. `GIR-V060` checks fresh-run provenance, no receiver dependency and proven emptiness for `x_replace` (not S9 destination linearity). `GIR-V100` requires the stated origins and profile-correct abort kinds. No new malformed record can bypass a check by using `x_store` on the owner.

Core establishes demand and lifetime safety. GIR-H's verifier checks the operation contracts and summary annotations, but does not rederive `V-SHRINK` from arbitrary CFGs. A type-correct manually forged GIR-H module containing a live alias across a shrink can still pass those structural checks and fault on execution. Only the Core-to-GIR-H lowering theorem for validated `core-shrink`, or an independently validated instance with that provenance, supplies the lifetime claim; a standalone verifier result must not be advertised as one.

#### GIR-L header and stack lowering

Grow/growshrink owners use §11.1's `{base,len}` header and own data stack. With fixed element size `s` and checked new length `n`, shrink lowers to a stack release to `base + n*s` and header length publication in Core order; clear releases to base. Pop first snapshots `s` bytes at `base + (len−1)*s` before release. Resizable by-reference parameters retain their header address plus stack identity, so a callee changes the caller's same header/stack, not a copied header. The per-stack ownership and scope watermark obligations of `GIR-V090` still apply; a reduction through a by-reference owner may release only that passed owner's stack, never an unrelated caller watermark. Recursive-resizable support remains §11.1's explicit boundary.

A limited owner has reserved frame/global byte storage: the frontend's authoritative length-prefix layout followed by `k` element slots. Use the existing `LenStore`/array layout calculation to choose the smallest unsigned length field fitting `k` and its byte offset/total size; do not create a second packing rule or use a resizable header. Its by-reference argument is one address, with capacity static in its type. Initialize/write only the length and provided elements; unused slots are uninitialized. Shrink emits only a length-field store, never `l_release`, zeroing, moving, or clearing retained element bytes. Growth overwrites slots starting at the old visible length. As with packed structs, potentially unaligned scalar accesses use byte-copy loads/stores.

All runtime checks lower to explicit compares/branches ending in `t_abort` with the kind/origin above. Resize's size reinterpretation for the negative check uses wrap semantics in both numeric profiles; it is not a checked source cast. For resizable growth, allocate the added byte run using `l_bump`, fill/copy it and publish header length. For limited growth, branch on capacity before stores and fill/copy reserved slots. `x_replace` copies its fixed-element transient run into the cleared resizable's region and publishes length; its operands contain neither a destination handle nor a receiver construction trace. Partial-run allocation caused by an abort is terminal and does not restore or publish a later length.

GIR-L adds no type/tag, descriptor table, module field, or `l_rt` entry. Limited owners are `m_bytes`/`lglobal bytes` with authoritative byte size; grow/growshrink use existing `m_header`/`lglobal header`. Existing address, scalar, copy/fill, header and stack instructions suffice. The profile gates the five abort kinds in the unchanged low `t_abort` arity. This subsection does not define the nonfixed destination, staging, result delivery or construction trace of §7: those remain the construction profile's separate contract.

### 12.8 Construction in goose-core/0.2, core-construction

This profile inherits the completed `core-shrink` tags, nominal struct descriptors, shrink rules and limits. It adds the records below, selected by the exact schema/profile pair before decoding tables. Pilot and shrink record shapes and bytes are unchanged. An S9 tag under either earlier profile, or a construction module with an earlier profile's arity, is `malformed`. Support is claimed only when each inherited and added feature runs through export, validation, semantics and native GIR; this contract alone establishes no gate.

#### Module, results and targets

`impl_id` and `target_id` are `nat` indices into the implementation and nonlocal-target tables. `Request` is the closed enumeration `register value element_run`; `register` is required for fixed, reference or slice results, `value` or `element_run` for nonfixed array results. `element_run` is legal only when the result is an array; its logical element type is the result array's element type.

| Tag | Fields | Meaning |
|---|---|---|
| `module` | `str` schema (`goose-core/0.2`), `str` profile (`core-construction`), `[file]`, `[Ty]`, `[struct_def]`, `[target]`, `[global]`, `[impl]`, `[context]`, `ctx` entry, `[origin]` | Exactly eleven fields after the tag; structs and targets are mandatory, even when empty. |
| `struct_def` | `nat` byte size, `[field]`, `str` display name | The construction profile requires a nonempty UTF-8 nominal display name. Struct table identity remains nominal; the name controls rendering. Earlier profiles retain their existing descriptor arity. |
| `target` | `[impl_id]` members | Nonempty, sorted, duplicate-free exact member set. All members have identical result types and requests. The result protocol is taken from the first member; there is no second signature to disagree with it. |
| `impl` | `str` name, `[param]`, `[result]`, `[local]`, `block` body, `Summary` | Same six-field arity as the pilot; the profile selects result descriptors instead of bare result types. |
| `result` | `ty`, `Request`, `[var]?` named local | Exactly one descriptor per result position. The optional local is allowed only for a nonfixed result and is checked for destination alias eligibility below. |
| `summary` | `[Target]` reads, `[Target]` writes, `[Target]` grows, `[Target]` shrinks, `[Target]` rebinds, `[nat]` constructs, `[target_id]` needs, `[target_id]` escapes, `flag` aborts, `flag` outputs | Exactly ten fields. All lists are sorted without duplicates; target lists use the existing `t_param`/`t_global` ordering. `constructs` names nonfixed result positions, not ordinary parameter roots. `needs` names targets that must be supplied by an enclosing activation; `escapes` names targets this implementation may propagate to its caller. |
| `summary_unknown` | none | Still distinct. It implies every storage effect, construction, external target requirement and escape; it cannot justify a plain nonescaping call or waive target availability checks. |
| `varr` | `ty` element | `T[]`, default fixed-width `u32` length prefix. The element may be flat fixed or recursively variable. |
| `r_static` | none | Immutable static byte literal storage; outlives every activation and global. No write, grow or shrink can target it. |

Constructible nonfixed types are `varr E`, `grow E`, and fixed `arr E k` whose element `E` is recursively variable, plus inherited grow-shrink arrays of flat fixed elements. For `varr` and `grow`, `E` may be flat fixed or a recursively variable value; recursively variable values are `varr` and fixed arrays of recursively variable elements, so `u8[][2]` is constructible but is not flat fixed. Grow-shrink variable elements remain outside this profile. Limited arrays retain fixed slot size, so a variable element there is rejected by `V-TYPE`. Flat struct descriptors remain flat fixed; nonfixed struct fields and resizable elements remain outside this profile. Prefix-width annotations other than the default array representation are `unsupported: array-prefix`; `varint` remains separately excluded. This does not silently reinterpret a source `T[u8]` as `T[]`. References and slices stored in elements or fields remain excluded.

String values have no special `Ty`. `u8` arrays and slices are strings; raw bytes need not be UTF-8. UTF-8 requirements on diagnostic paths and names remain lexical requirements and do not apply to literal data encoded as byte lists.

Context numbering follows §12.1 and includes calls in construction operands and forwarded multi-result calls. Target ids are assigned at first mention while walking implementations in id order, fields in document order (including summaries after bodies); equal member sets are interned. The referenced implementations are assigned by the context walk first, so target numbering never changes function numbering. Target-only implementations must already be reachable checked specializations; the exporter does not instantiate them. In type numbering a result descriptor mentions its `ty` where a pilot result type did; array element types precede parents. `r_static` sorts before `r_local`, `r_global`, `r_param` in root lists; it does not add a variable table row. Module table indices may refer forward; type component ordering still applies.

#### Construction and result syntax

Existing `s_let`, `e_push`, `s_assign_whole`, `e_arr`, `e_fill`, `e_if`, `e_block` and `e_call` become destination-aware when their resolved result is nonfixed. The optional tail of a block still holds one expression; `e_values` represents several results. Nonfixed `e_read` is rejected: a storage-to-value transfer must be an explicit copy or returned-local form. `v_of`, `.len`, indexing and slicing also accept `varr`, and views may have variable element types without copying those elements. A `for` that visits a nonfixed element binds it by reference.

| Tag | Fields | Meaning |
|---|---|---|
| `e_bytes` | `ty` resolved result, `[nat]` bytes, `org` | Each byte is 0..255. A `slice const u8` result views immutable static storage with root `r_static`; a receiving `u8` array type initializes its destination with those literal bytes, with fixed count/capacity checked. An origin identifies the source construct, not the identity of its pooled bytes. |
| `e_arr`, `e_fill`, `e_if`, `e_block` | Existing fields followed by `org` | Construction records append their source origin, including implicit tails and nested empty constructors. Earlier profiles retain their existing arities. Lowering uses this origin for child, staging and checking operations. |
| `pa_view` | `View` | Sample and render an existing array/slice run, including nonfixed storage, without a detached value. |
| `e_str` | `ty` receiver array type, `[PrintArg]`, `org` | Construct text directly into a `u8` array destination. `pa_expr` evaluates and renders its operand before the next argument runs; `pa_text` writes its UTF-8 bytes. Raw literal bytes use `e_bytes`. No detached builder is made. |
| `e_copy` | `ty` receiving type, `Place` source, `org` | Resolve the source once, copy its completed value into the destination and emit `copy`; an array/slice source can adapt to an array-family receiver with the same element type. Check limited capacity before out-of-slot writes. A flat source remains an ordinary snapshot copy. |
| `e_result_local` | `var`, `org` | Only in a result position of `s_ret_values`, a body tail, or `e_values` there. Returns a local's completed nonfixed value: no ordinary copy if the matching result descriptor aliases it; otherwise one `copy`. It cannot return a parameter or a foreign local, or be used as an ordinary by-value argument. |
| `a_construct` | `Expr` | A nonfixed by-value parameter's argument, built at the call site's reserved parameter storage in argument order. It replaces `a_val` for that parameter. |
| `e_values` | `[Expr]` | At least two result operands, evaluated left to right into distinct receiving channels. Not a source-storable tuple. Each operand produces one result. |
| `s_receive` | `[var]`, `Expr` producer, `org` | At least two newly declared variables in the same scope, receiving a multiple-result `e_call` or `e_values`. Variable count/types match producer results. All receiver identities are fixed before evaluating the producer, and nonfixed results construct in those variables' own storage. |
| `s_append_value` | `Place` receiver, `Expr` fixed array producer, `org` | Resolve receiver, evaluate the complete fixed snapshot (including a register-result call), then append its elements. No result destination enters the producer. |
| `s_append_construct` | `Place` receiver, `Expr` nonfixed array producer, `org` | Resolve receiver once, open an `element_run` destination, evaluate the producer there, then publish the complete run and update length once. This is distinct from inherited `s_append`, which copies a sampled source view. |
| `s_ret_values` | `[Expr]`, `org` | Zero or more single-result operands, matching the enclosing implementation's descriptors. Evaluate left to right; land completed nonfixed results, leave scopes, return. The pilot `s_ret` remains legal for zero or one result only. |
| `s_ret_forward` | `Expr` (an `e_call`), `org` | Forward one call's complete result list into the enclosing result channels without introducing a tuple or copying fresh results. |
| `s_return_from` | `target_id`, `[Expr]` result operands, `org` | As `s_ret_values`, using the target's descriptors and innermost active receiver channels. |
| `s_return_from_forward` | `target_id`, `Expr` (an `e_call`), `org` | Forward all call results into that target's channels. |
| `s_break_value` | `Expr`, `org` | Leave the innermost value-producing loop/block, constructing into its saved destination and applying `C-ABANDON`; inherited valueless `s_break` remains unchanged. |

`e_arr`'s explicit type may now be variable or resizable, with any number of elements including zero; a fixed result still requires its exact declared count. Each nonfixed element gets a nested `value` destination and completes before the next initializer. A fill evaluates one completed source and copies it repeatedly; the repeat count must already be available from its resolved fixed type. A branch or block forwards the same result channels to the selected arm/tail. An array-producing call must have a request matching the actual receiver; the exporter chooses the checked specialization or destination-request twin, and MUST NOT drop the request distinction to share implementations.

`pa_expr`/`pp_val` additionally render `u8` arrays/slices verbatim. `pa_view` lowers to a sampled view operand accepted by `pp_val` or `x_dest_text`. Other supported aggregate rendering follows language spec §3.7 structurally (field order, delimiters, nominal type name, decimal scalars); no user-defined formatter or excluded value is smuggled into an opaque text operation. `print` renders arguments in order and writes one joined line after all complete, as decision D-1 requires. A print operand may name a nonfixed place through `pa_view`; it cannot require an illegal detached `e_read` value.

Every receiver operation publishes only after all its normal results are complete, with separate `publish` events in result-position order for a multiple receive. An escape before normal completion publishes none of that operation's pending normal channels. Earlier completed statements remain observable. A callee completing a result does not itself make the receiver's array length or variable live; the receiver publishes it once. Targeted return results finish and land before that target's caller publishes them.

#### Named results, roots and effects

For each nonfixed `value` result, the exporter uses structural named-result discovery on the checked unoptimized body (`NamedResultOf`, `DetectNrvo`) and exports the chosen alias in `result`. The independent validator recomputes eligibility. Candidates are single-name locals declared directly in the body scope, not parameters, branch locals, or multi-name receives. Every explicit return to this implementation and its normal value tail is examined per result position. A direct returned local must be the same candidate at all such sites; every other returned expression must have no direct or alias/callee access to that candidate. Unknown access and captures conservatively prevent the alias. All direct returns are last uses. One local can alias at most one result; result positions are examined left to right. Missing an alias that this discovery requires is also a validation failure, because guaranteed construction cost is observable. Its type/layout must equal the receiving type, or be a resizable array of the same elements returning as `varr` with a reserved receiving prefix. Type-only equality cannot merge nominal types or alter prefix storage.

For `element_run`, the descriptor has no named alias: legacy `EmitSpec` disables `DetectNrvo` in its element-run form. A local that was operated on as a whole is built in its own storage and copied once into the requested run on return; a forwarding fresh constructor still passes the run destination directly. A packed value constructed in receiving storage can instead use header removal. These are the explicit destination-request exceptions in language spec §7.3, not permission to stage arbitrary fresh results. Different returned locals prevent aliasing for a `value` position; whichever path executes makes one ordinary copy. An independent fresh alternate return keeps the alias and uses abandonment plus `exit-value` landing over the already-built local. A forwarding multi-result call conservatively prevents discovery for its forwarded positions, matching the existing warning. This conservative boundary is part of the construction-cost comparison; it is not an optimizer inference license. An alias under `element_run` is rejected even when value-form discovery would choose that local. A forged alias is rejected even when it produces the same final bytes.

Receiver storage and a result's incoming destination are ownership capabilities, not reference roots exported as ordinary values. Nonfixed results contain no stored references in this profile, so their `result-roots` entry is empty. References/slices returned normally or nonlocally still obey `V-RESULT`: only parameter/global/static backing storage that outlives the receiver is allowed. For a targeted result, `r_param` means the target activation's argument root, not the helper's argument at the same numeric position; validation maps it through the call path. A reference into a parameter constructed by value is a local root and cannot escape that activation. A reference or slice into a local abandoned by an exit is rejected. Reference results into sibling nonfixed result storage are `unsupported: result-interior-reference` until their root relation is explicitly modeled.

`constructs` contains each nonfixed result position that a normal return may complete, including a caught targeted return. Building a local/argument is local storage effect; copying reads its source roots, and publishing push/append grows the receiver roots. Writes, growth and shrink of a named-result local stay local during construction; they do not pretend to be a written by-reference parameter. The separate construction annotation describes its result channel. An escape's target construction is attributed to its target channels, never to the helper's own `constructs` positions. `aborts` includes inherited checks and capacity checks; output includes text evaluation's transitive output and actual print operations.

A return-from adds its target to `needs` and `escapes` unless this implementation itself handles it. A call adds the callee's target lists, removes targets handled by this implementation, and checks every remaining requirement against all possible enclosing call paths. The least required target sets are computed from bodies and recursive calls; annotations must contain them, and conservative extra `needs` must also be available at every call. At a global initializer or the entry, no external target requirement is available. Target membership is checked independently of summary assertions. Root annotations and effect summaries remain checked per context; execution uses only implementations, receiver channels and target tables.

Decoding rejects profile-selected arity/tag errors, byte values above 255, empty/repeated/unsorted target sets, target/member/result/alias indices outside tables, wrong enumeration values and unsorted summary lists. Type/permission errors, invalid aliases, missing target availability, incomplete result lists and forged effects are validation failures (`V-TYPE`, `V-MUT`, `V-RESULT`, `V-CALL`, `V-SUMMARY` or construction/exit rules), not malformed JSON.

### 12.9 Construction in gir-h/0.4, core-construction

This profile inherits the completed GIR-H shrink contract and selects the following module/signature shapes. Core target ids, member order, result positions, scopes and slots are retained; member implementation ids become the corresponding function ids. Global initializer functions appended by the lowering are never target members. The same lexical and size limits apply. `dest`, `built` and `cancelled` are SSA-only protocol types, never data types, slot types, struct components, stored values, source arguments or source results.

The exact JSON operands for adapter, published-reference, and target-exit records are listed in the [construction GIR wire note](goose-ir-construction-wire.md).

| Tag | Fields | Meaning |
|---|---|---|
| `module` | `str` schema (`gir-h/0.4`), `str` profile (`core-construction`), `[file]`, `[Ty]`, `[struct_def]`, `[target]`, `[global]`, `[func]`, `fn` entry, `[origin]` | Exactly ten fields after the tag. |
| `struct_def` | `nat` byte size, `[field]`, `str` display name | The same construction descriptor as §12.8. |
| `target` | `[fn]` members | The Core set renamed through lowering. |
| `func` | `str` name, `[ty]` source params, `[result]`, `[slot]`, `[scope]`, `[block]`, `roots`, `Summary`, `[org]?`, `[certificate]?` | Same ten-field arity as §12.2; the profile selects descriptors instead of bare result types. `result` has Core's fields with a named `slot` instead of `var`. |
| `dest`, `built`, `cancelled` | `ty` nonfixed receiving type, `Request` (`value` or `element_run`) | An open linear destination, a completed value awaiting publication/return, or a linear certificate that the pending normal destination was abandoned on an escape path. |
| `i_bytes` | `val` result, `[nat]` bytes, `[org]?` | Static `slice const u8`; byte range and static roots as in Core. |
| `i_result` | `val` result, `val` call result pack, `nat` result position | Project one carrier; a nonfixed component is projected exactly once. The pack is SSA-only; it has tuple carrier types and cannot be stored. |
| `x_append_value` | `val` receiver reference, `val` fixed array snapshot, `[org]?` | Append the completed fixed array elements after its evaluation; no source-visible temporary slice. Needs an origin. |
| `i_dest_open` | `val` result, `DestReceiver`, `ty` logical producer type, `Request`, `[val]?` known count, `[org]?` | `dest T R`. Resolve/check storage once; save its start, owner and actual receiving layout. When the producer and receiver are different array families, require identical element types and retain the receiver metadata adaptation; the handle/carrier has the producer type/request while publication stores the receiver representation. An optional count is a nonnegative integer number of elements checked against available capacity. Needs an origin. |
| `dr_slot`, `dr_global` | `slot`; `glob` | Fresh variable/global storage, request `value`, existing storage not yet initialized. |
| `dr_push`, `dr_append`, `dr_whole` | `val` receiver reference | An element, appended run, or replacement in resolved array storage. Requests are respectively `value`, `element_run`, `value`; whole assignment shrinks first under `V-WHOLE`. |
| `dr_arg` | `fn` callee, `nat` parameter position | A call-site nonfixed parameter region. Its completed value is owned by that call, not reused by another. |
| `i_dest_child` | `val` result, `val` parent dest, `ty` element, `[org]?` | Nested `dest E value` for the next nonfixed element. Suspends parent writes until child completion. Needs an origin. |
| `x_dest_write` | `val` dest, `val` fixed element, `[org]?` | Write its next logical element; no publication of the receiver operation. |
| `x_dest_attach` | `val` parent dest, `val` child built, `[org]?` | Consume the next completed nested element, resume the parent. |
| `x_dest_bytes` | `val` dest, `[nat]` bytes, `[org]?` | Initialize a `u8` destination from literal bytes, emitting logical writes without an ordinary copy event; byte range/count/capacity checks as in Core. |
| `x_dest_text` | `val` dest, `val` rendered scalar or sampled view, `[org]?` | Append that operand's text bytes to a `u8` destination before the next operand evaluates. |
| `x_dest_copy` | `val` dest, `val` source reference or sampled view, `[org]?` | Copy completed storage once into this destination; emits ordinary `copy` and retains logical element order. Needs an origin. |
| `x_dest_repeat` | `val` dest, `val` completed source built, `[org]?` | Fill a fixed-count destination from one completed source. Borrow its bytes for each repetition, emit repeat-source copies, then consume and release the private source. Needs an origin. |
| `x_dest_snapshot` | `val` dest, `val` fixed array snapshot, `[org]?` | Write the already evaluated snapshot's elements in order. Emit fresh writes without an ordinary storage-copy event. Needs an origin. |
| `i_render` | `val` result, `val` operand, `[org]?` | Immediately render a scalar, fixed aggregate or sampled view into an immutable `u8` view. Its statement-owned scratch has no construction events or storage ordinal. Only print and text consumers may use it; it cannot escape. |
| `i_dest_finish` | `val` result, `val` dest, `[org]?` | Consume open `dest T R`, produce `built T R`; final metadata/count are now known, receiver is still unpublished. |
| `x_dest_bind` | `slot` named local, `val` built, `[org]?` | Consume its initial completion, bind the declared named local at the incoming result storage without publishing to the caller. Its metadata becomes local state and ordinary permitted mutation/growth can continue there. |
| `i_dest_named` | `val` result, `slot` named local, `[org]?` | At that result position's last-use return, consume the local ownership and produce `built T R` with its current metadata; no ordinary copy. |
| `i_result_exit_dest` | `val` result, `nat` result position, `[org]?` | `dest T R` for this activation's nonfixed result descriptor. Begin a replacement at the current top of its incoming receiving storage, retaining the original receiver/layout and landing start. Suspend its bound named local or partial normal construction; no `TargetId`, target table entry, or active-target lookup is used. Only cleanup may use the superseded destination handle; existing source references remain readable until their portion is abandoned, subject to the usual root checks. The selected named alias already requires alternate expressions not to reach that named local. Needs an origin. |
| `i_dest_abandon_named` | `val` result, `slot` named local, `val` completed replacement, `[org]?` | After that replacement is complete, consume the suspended bound-local ownership, emit `abandon` for its old portion, and produce its `cancelled T R` certificate. Protect the replacement interval from restoration; the replacement carrier stays live for landing. Needs an origin. |
| `i_dest_arg` | `val` result, `val` built, `[org]?` | Consume a `dr_arg` completion, publish its parameter region, and yield `ref mut T` with exclusive call-argument ownership provenance. It must be transferred exactly once to the specified callee/parameter, with no other use. |
| `x_dest_publish` | `val` built, `[org]?` | Consume a non-argument completion carrier and publish to its recorded receiver exactly once. For an array operation this updates live length. |
| `i_dest_abandon` | `val` result, `val` dest or built, `[org]?` | Consume/discard this unpublished portion, children first; emit `abandon` once and restore its start, preserving in-flight escape intervals. Produce `cancelled T R`. |
| `x_dest_cancel` | `val` cancelled, `[org]?` | Consume the abandonment certificate at its owning receiver, without another `abandon` event or byte restore. |
| `i_dest_value` | `val` result, `val` dest, `[org]?` | Consume `dest T element_run` and construct a packed value in the same receiving storage, yielding `dest T value`; retains the original run request/start, emits no second `begin`, and requires removable metadata. |
| `i_dest_relocate` | `val` result, `val` built, `str` reason (`header-removal` or `exit-value`), `[org]?` | Consume and replace the carrier after in-place adaptation/landing. Header removal converts `built T value` from `i_dest_value` to `built T element_run`; exit landing retains type/request. Arbitrary movement is rejected. |
| `i_dest_stage` | `val` result, `val` limited dest, `str` reason (`capacity-check`), `[org]?` | Temporarily suspend the limited destination and construct in its private stage, yielding a `dest` of the same receiving type/request. Legal only when length is not known before evaluation; it retains the same logical trace destination and emits no second `begin`. Needs an origin. |
| `i_dest_fit` | `val` result, `val` staged built, `[org]?` | Check capacity, copy into the suspended limited receiver, consume the staged carrier, produce a receiver `built` carrier. Overflow aborts without out-of-slot writes; needs an origin. |
| `i_call_construct` | `val` result, `fn`, `[val]` source args, `[val]` result dests, `[org]?` | Normal-only call with at least one nonfixed result. Consume each result destination, pass it to the callee, and produce the ordered result carriers (one carrier directly, or a tuple pack). Needs an origin. |
| `i_target_dest` | `val` result, `target_id`, `nat` result position, `[org]?` | An exit destination at the current top of the innermost active target's receiving storage, with its saved receiver start retained for landing. It temporarily supersedes that activation's pending normal channel; it never duplicates a usable ordinary channel handle. Only for a statically available target; needs an origin. |

`i_call` remains for normal-only calls with exclusively register results; several register results use an SSA tuple pack and `i_result`. A nonfixed by-value source parameter is passed as the owned reference produced by `i_dest_arg` to its completed call-site storage, with the source parameter's original nonfixed type retained in the signature. Block 0's carriers are source parameters in order (nonfixed by-value parameters as `ref mut T`), followed by incoming `dest T R` channels for nonfixed results in result-position order. These hidden channels are not additional source parameter positions: `r_param` and `t_param` indices continue to index the written and closure-converted source parameters. A by-value nonfixed parameter's entry carrier is rooted at its local parameter slot for lifetime/effect checks, not at the caller's argument source; reads used to construct that source were already evaluated by the caller. Returning a reference into this storage is invalid. The receiver references for `a_construct` must come from the immediately associated `dr_arg` completion via `i_dest_arg` and transfer exactly once to that call. Ordinary borrowed nonfixed arguments remain `ref` parameters.

A result carrier is its ordinary value for `register`, and `built T R` for a nonfixed result. Fixed carriers may be copied/projected normally; each nonfixed pack component is projected once and consumed once. A result destination transferred to a call is unavailable to the caller until a returned completion carrier arrives. Passing it to a nested call is the meaning of abstract `dest.pass`; it is not a second open/publish and does not erase the obligation to finish or abandon. Callee `ret` transfers completion ownership back; the receiver publishes it. Named-result slots alias incoming channels and are never initialized by `x_init` with detached bytes. Their declaration finishes initial construction and uses `x_dest_bind`; subsequent mutations affect the locally owned value, and `i_dest_named` completes the return channel at its last use. The verifier distinguishes this bound-local ownership state from an open element destination or a returned/published completion. Scope leave removes their local names while preserving receiving storage. Ordinary nonfixed slots similarly use open/finish/publish, with `x_init` restricted to fixed/reference/slice values.

A normal alternate return beside a bound named result uses `i_result_exit_dest` for each replacement result position, constructs and finishes its independent expression there, then `i_dest_abandon_named` and `x_dest_cancel` discard the suspended local ownership. `i_dest_relocate` with `exit-value` moves the completed replacement down to the saved incoming result start, producing the carrier passed to `t_ret`. A normal return from a partially built result uses the same exit destination, then ordinary `i_dest_abandon`/`x_dest_cancel` on the superseded open portion with the replacement interval protected. Result operands are evaluated left to right before their needed sources can be discarded. A direct last-use return of the named local still uses `i_dest_named`, without replacement or relocation. This protocol applies to plain `s_ret_values`, normal body tails and forwarded alternate returns; none needs to register the current function as a nonlocal target.

The replacement has a fresh dynamic destination id and `begin` event; the old named/partial destination is abandoned once. Its completion retains the same receiving owner/channel, so after landing it can fulfill that original call result even though its trace id differs. The receiver publishes the replacement exactly once. `GIR-V060` requires the replacement's saved channel and original start to equal the superseded result position, prohibits further named-local use, and requires old cancellation before landing/return; matching only the carrier type is insufficient. If an alternate expression aborts, the trace ends with both old suspended ownership and replacement construction intact, without fabricated abandonment.

| Terminator | Fields | Meaning |
|---|---|---|
| `t_invoke` | `fn`, `[val]` source args, `[val]` normal-result dests, `block` normal, `[val]` normal forwarded args, `[escape_edge]`, `[org]?` | Call required when callee may escape. On normal completion, pass callee result carriers first, followed by forwarded args. On escape, follow exactly the matching target edge with that target's carriers first, then one `cancelled` carrier per nonfixed normal-result destination in result-position order, then its forwarded args. Needs an origin. |
| `escape_edge` | `target_id`, `block`, `[val]` forwarded args | Edges sorted by target id, exactly covering callee's possible propagated targets; target types/requests determine leading block parameter types. |
| `t_ret` | `[val]` result carriers, `[org]?` | Types/requests match current function's descriptors; no scope entered. Transfers completed destination ownership to caller, never publishes twice. |
| `t_escape` | `target_id`, `[val]` target result carriers, `[val]` cancelled normal-result channels, `[org]?` | No scope entered; current function is not a target member; propagate target carriers and cancellation certificates for this function's own nonfixed normal-result channels, in result-position order, without publishing or restoring target-owned storage. Needs an origin. |

An invoke escape successor for a member of its target lands the results, abandons that activation's unfinished normal construction, leaves scopes, and ends in `t_ret`. A nonmember successor abandons only its own unfinished normal channels, leaves scopes, and ends in `t_escape`. The target results use target receiver channels and are not the callee's pending normal results. Abandonment of overlapping storage excludes the escaped value's live interval, then `exit-value` landing closes the gap. An escaping callee explicitly abandons each incoming normal channel it still owns before `t_escape`; a channel passed to a nested invoke returns as a cancellation certificate instead of as a usable normal destination. The escape edge therefore receives typed cleanup ownership, not an inaccessible token. An owning receiver consumes that certificate with `x_dest_cancel`; an intermediate function forwards it as its own corresponding normal-channel cancellation when the destination was passed through. Its separate unfinished parent/argument/local destinations are abandoned and their certificates consumed. Each logical destination emits `abandon` once across the whole unwind, and no cancelled channel can become a normal result. Any saved destination or reference passed through an edge must be in its explicit forwarded operands or dominate that edge.

Reference lowering is destination-directed. It opens the resolved receiver before a nonfixed constructor; `e_bytes` as a slice lowers to `i_bytes`, while array-form `e_bytes` lowers to `x_dest_bytes`. It lowers elements and branches in source order, finishes and publishes at the receiver operation. It emits source arguments in order, constructing each nonfixed parameter region and emitting `i_dest_arg` before advancing to the next argument; callee invocation follows all arguments. Result channels for a call are supplied in result order. A nonescaping call uses `i_call`/`i_call_construct`; an escaping call creates its normal continuation first, then target-specific escape blocks in ascending target-id order, and emits `t_invoke`. `s_ret_forward` passes current channels to the forwarded call; `s_return_from_forward` obtains the target channels first and passes those. Plain alternate returns use the current-activation replacement protocol above; nonlocal returns use `i_target_dest`. Returns and value-bearing breaks land values before leaving scopes; a destination has no owner-local watermark restored by a callee. No staging is emitted for an unbounded receiver. An incoming-channel constructor emits neither a redundant `i_dest_open` nor a second `begin` event.

`GIR-V010` checks carrier types, signature channel arity, element restrictions and nominal layouts; `GIR-V020` checks all normal and escape edge parameters/dominance, including implicit result carriers; `GIR-V030` checks receiver ownership and contents capability. `GIR-V040` applies to `t_ret` and `t_escape`, including caught invoke edges. `GIR-V050` derives storage, result-construction and target effects from bodies, maps source parameter indices through actual arguments, and checks annotations before using them. `GIR-V060` proves path-linear destination ownership, child ordering, exactly-once completion/publication/abandonment, justified staging/relocation, named aliases, no post-completion writes, and `C-NOGROW` through mapped summaries. It treats terminal abort/exit as trace-ending paths. `GIR-V070` checks active targets on all call paths, complete target-typed results, exact escape-edge coverage, and catches only by members. `GIR-V090` rejects any watermark restore that crosses incoming, passed or escaped receiving storage. All new checking/call/escape operations require origins under `GIR-V100`.

The concrete layout, low encoding and nonlocal protocol in §12.10 replace all these protocol operations. A remaining destination/completion/cancellation type, invoke or escape in GIR-L is rejected by `GIR-V090`; it cannot be emitted as an opaque operation.

### 12.10 Construction layout and protocol in gir-l/0.2

The construction profile inherits scalar/address operations and checked control flow from §12.3, and selects the module and records below. No high type or destination carrier survives. Primitive `ptr` size is a module target property; native emission checks it against the selected C target. Scalars and array length prefixes use the language's little-endian packed representation, with unaligned accesses emitted through byte-safe loads/stores; native ABI pointer fields and frame metadata are outside serialized Goose value bytes.

| Tag | Fields | Meaning |
|---|---|---|
| `module` | `str` schema (`gir-l/0.2`), `str` profile (`core-construction`), `[file]`, `[Ty]`, `[ltarget]`, `[lglobal]`, `[lfunc]`, `fn` entry, `[fn]` initializers, `nat` stacks, `nat` global stacks, `nat` pointer bytes (4 or 8), `[origin]` | Exactly thirteen fields after the tag. The low type table contains only integer/bool/unit/ptr types. Earlier profiles retain §12.3's shape. |
| `ltarget` | `[fn]` members, `[ty]` cells, `[lchannel]` result channels | A concrete thread-local target record, one typed scalar/address cell per entry, no high types. Cell 0 is `bool active`; remaining cells are assigned in result order as below. All members have identical lowered result ABI. |
| `lchannel` | `nat` result position, `[nat]` incoming cells, `[nat]` escaped-value cells | Positions are dense from zero; lists index this target's cell table. Incoming cells hold that activation's normal receiving channels. Escaped-value cells hold the completed nonlocal payload until catch. |
| `m_dynamic` | `nat` stack, `nat` scope, `str` name | A frame address member for a variable-size local's packed value, whose bytes live on the assigned stack; no detached aggregate SSA value. Globals of this kind use `["lglobal", name, "dynamic", global_stack_index]`, with their assigned global-stack index. |
| `l_static` | `val` result, `[nat]` bytes | Address of immutable static byte data; length is a separate integer constant. |
| `l_rf_get` | `val` result | `i64` thread-local return discriminant: 0 means normal, target id + 1 means a nonlocal result in flight. |
| `l_rf_set` | `val` discriminant (`i64`) | Store that discriminant. Only 0 or an existing target id + 1 is legal. |
| `l_target_load` | `val` result, `nat` target, `nat` cell | Load the primitive type specified by this target cell. |
| `l_target_store` | `nat` target, `nat` cell, `val` | Store exactly the cell's primitive type. |
| `l_fmt` | `val` result, `str` kind (`int uint bool`), `val` scalar, `val` destination address | `i64` formatted byte count. A thin closed runtime formatting operation; scalar type/sign matches its kind, writes text at the supplied byte address. |
| `l_out_bytes` | `val` data address (`ptr`), `val` byte count (`i64`), `[org]?` | Emit exactly that many bytes to stdout in one length-based output operation; count is nonnegative and the complete source interval must be live. NUL has no terminator meaning and bytes are never decoded as UTF-8. Needs an origin. |
| `l_source_new` | `val` result (`ptr`), `val` storage id (`i64`), `[val]` path (`i64`) | Create an immutable trace provenance record identifying a logical source object and path. |
| `l_source_child` | `val` result (`ptr`), `val` source record (`ptr`), `val` index (`i64`) | Extend the source path. |
| `l_source_enter`, `l_source_leave` | `val` result token (`ptr`); `val` token (`ptr`) | Enter or leave a trace-record ownership scope. Leaving releases its records after retaining any transferred result records. |
| `l_source_param` | `val` result (`ptr`), `nat` primitive parameter position | Read this invocation's borrowed source record. Positions exclude the hidden stack base. |
| `l_source_call_push` | `val` result token (`ptr`), `[[val]?]` argument records | Create a call shadow frame. There is one optional source record per primitive argument after the stack base. Scalar, fixed and owned arguments have no borrowed source record. |
| `l_source_call_pop` | `val` token (`ptr`) | Release the matching call shadow frame after adopting returned source records. |
| `l_source_result` | `nat` primitive output channel position, `val` source record (`ptr`) | Retain source provenance for a returned address across callee cleanup. |
| `l_source_call_get` | `val` result (`ptr`), `val` call token (`ptr`), `nat` primitive output channel position | Adopt the callee's returned source record before popping the call frame. |
| `l_source_copy` | `val` source record (`ptr`), `val` destination id (`i64`) | Emit a storage-copy observation using the complete logical source path. |
| `l_trace_id` | `val` result, `str` kind (`storage destination`) | `i64` dynamic ordinal for the observation trace only; independent counters start at 0. Storage creation, including private capacity-check stages, and destination begin use their respective counters. Native code may elide it when no trace is requested. |
| `l_event` | `str` event kind, `[val]` primitive operands, `str` reason | Construction observation marker: `begin/publish/abandon` take destination id; `write` takes destination id/index; `relocate/stage` take destination id and their reason; `copy` takes source storage id, zero or more path indices, then destination id, with reason `storage`, or source destination id/destination id with reason `repeat`. Ids come from `l_trace_id`; all operands are integers. These lower to the event records of §12.11. It changes only the observation trace, never program stdout, value storage or control flow. Native tracing is emitted only for an explicitly requested construction-trace artifact; `storage` ordinals are assigned at each dynamic global/parameter/local object creation, including private capacity-check stages, and `destination` ordinals at each begin, even for empty values. |

`m_dynamic` uses one address field, plus existing mark/release operations for its assigned stack. Resizable local headers remain `{base, len}` outside their elements. A `varr E` packed value is `[u32 count][packed E elements]`; a fixed array of variable elements is the concatenation of its statically counted packed elements without a count prefix. Packed variable elements carry their own nested prefixes. There is no offset table: indexing element `i` scans from the sampled element base, applying the recursively compiled element-size walk `i` times. The bounds check uses the sampled count first. A slice keeps the sampled element address/count, not an index into the receiver's current header. Variable elements never change size after publication, so their addresses remain stable on permitted growth.

For a flat fixed element the walk adds its authoritative fixed byte size. For `varr E`, it byte-safely loads the `u32` count, adds four bytes, then walks `E` that many times. For a fixed array of variable elements it walks the element the fixed count times. Nested walks lower to ordinary CFG loops, `l_load`, `l_offset`, arithmetic and comparisons; no runtime `sizeof` query or unresolved traversal instruction remains. Copying/relocation measure the byte interval by this walk or by saved start/end marks and use `l_copy`/`l_move`. A nonfixed fill walks one completed source once for its byte size and repeats its bytes; it never reruns the initializer. Stack/capacity arithmetic is checked before a write and length publication; `u32` prefix overflow is a `capacity` abort. Grow-only variable elements append packed bytes at the same stack top; shrinking supported flat-element grow-shrink owners computes the retained byte boundary before releasing its suffix. Limited fixed-element receivers measure free element slots, not packed byte count.

Trace provenance pointers and tokens are metadata, never program-memory addresses. The verifier rejects their use as ordinary loads, stores or pointer arithmetic. It checks scope and call nesting, token liveness, parameter positions and result transfer. Each recursive invocation has its own shadow frame. Borrowed arguments retain the caller's exact logical source even when several arguments share an address. By-value slice parameters receive their own descriptor storage ordinal. Native emission removes all provenance operations unless construction tracing is requested.

Construction stacks use a directory of stable, lazily created cells. Recursive activations advance their stack base by their owned-stack count. Growing the directory never relocates a cell. Return and escape restore ownership before cells are reused. Dynamic cells count toward resource accounting.

In this profile `lfunc` has eight fields after the tag: `str` name, `[ty]` params, `[ty]` results, `nat` stacks, `[member]`, `[nat]` scope parents, `[lresult]` normal-result descriptors, and `[block]`. The descriptor list is mandatory, including `[]` for functions and initializers without results. Its tagged records, source-type identities, output positions, and receiving checks are specified in [the native construction contract](goose-ir-construction-native.md#low-result-descriptors). Pilot and shrink retain §12.3's seven-field encoding. Construction uses the following fully lowered ABI instead of the pilot first-result rule. Parameter 0 remains the `i64` stack base. Source parameters follow in source order: scalars by value; flat fixed aggregates by pointer to an already-copied snapshot; references to fixed/variable storage by pointer; resizable references by `(header pointer, stack pointer)`; slices by `(data pointer, i64 count)`. An owned by-value variable parameter passes `(value pointer, stack pointer)`; an owned resizable parameter passes `(header pointer, stack pointer)` with header metadata in its reserved call-site frame storage. The callee owns these parameter values for lifetime checks, and cleanup cannot restore the caller's unrelated stacks. A parameter region's reservation remains in use from its construction through its call and is released by the call site's epilogue after the callee has finished.

Every source result uses explicit primitive output channels appended after source parameters, in result-position order; all construction-profile low functions return no C value (`results` is empty, `t_ret []`). A scalar fixed result uses a pointer to its scalar output cell; a flat aggregate uses a pointer to its byte snapshot; a fixed-storage reference uses a pointer to an address output cell; a resizable reference or slice uses two pointers to its two primitive output cells. A nonfixed result uses `(receiving stack pointer, saved start pointer, count-output pointer)`. The third pointer addresses a 16-byte metadata record: signed 64-bit count at byte offset 0 and destination id at byte offset 8. The caller initializes the id, forwarding retains it, and replacement completion updates it. The callee writes the final count before returning. Its request is compiled into the chosen function body: `value` retains the packed variable header/nested metadata, `element_run` emits only the outer elements and stores the element count separately. A local resizable result's `{base,len}` header is outside the element run; nested variable elements retain their headers. Completed byte count is `stack.top - start`. An array-family adaptation keeps the source result ABI/request: a grow value received as a `varr` reserves the receiving four-byte prefix before the callee writes its elements, then patches that prefix from the returned count; a `varr` value received by an external-header resizable writes in value form and removes its outer prefix in place before publication. Same-family `varr` reception writes exactly one prefix. These adapters use the same receiving stack, preserve named-result eligibility, and never materialize a separate fresh result. Result storage is resolved once before the call, so a second load of a receiver expression cannot select another destination. Fixed-array-returning calls use a fixed byte-snapshot output and then an ordinary element append; they receive no nonfixed stack/start/count channel.

For each fixed target result, its incoming target cells hold the same output pointers and its escaped-value cells hold the corresponding primitive value(s), or one pointer to a completed flat byte snapshot. For each nonfixed target result, incoming cells are exactly `(ptr stack, ptr saved start, ptr count output)` and escaped-value cells are exactly `(ptr value start, ptr value end, i64 count)`. These cell types and ordering are explicit in `ltarget`; `lchannel` maps positions without inferring a high type. The first available cell after `active` starts result 0's incoming cells, then its escaped cells, then result 1, and so on. Cell indices are never ABI byte offsets; the emitter lays typed native cells out and uses their names. A nonlocal fixed snapshot must survive intermediate epilogues in target-owned result storage, rather than a helper's frame.

A target activation's prologue loads and saves all its target cells into frame scalar/address members, writes `active = true` and installs its incoming result channels. Recursive activations repeat that save/install operation; they do not share the currently installed channel values. At return-from, low code reads the currently installed innermost target channels, evaluates result operands in order, writes the escaped-value cells only after each payload is complete, then sets the discriminant. A compiled call that may escape is an ordinary `i_call` followed immediately by `l_rf_get`, comparisons and branches to the statically enumerated target-specific paths. A normal path observes discriminant 0 and uses its normal outputs; an escape path never reads uncompleted normal output cells.

Before propagating, each frame abandons only its owned unfinished portions, protects the escaped payload's saved `[start,end)` intervals, restores its own scope watermarks and its saved target records, then returns with the discriminant unchanged. Restoration of an unrelated target record never overwrites the in-flight target payload. At a member catch, code first captures the payload cells, clears the discriminant, removes abandoned gaps with `l_move`, patches resulting prefix/count metadata, and writes its normal output channels. It then restores this activation's saved target cells and leaves scopes before returning. Thus the outer recursive target's channels are restored only after the inner payload has landed. Nonlocal result stacks stay in the caller's in-use set throughout; no intermediate `l_release` can cross them. Cleanup cancellation certificates become checked control-flow/mark bookkeeping, with no runtime aggregate and no duplicate release/event.

Normal receiver publication patches length/header metadata after successful construction. Whole assignment's initial shrink and its right-side exclusion follow `V-WHOLE`; fixed-element pushes evaluate before opening the receiver. Limited staging uses a distinct statically planned scratch region, one evaluation, a capacity branch before the receiving copy, and release of that stage after fit or escape. A known-size result branches on capacity before receiver writes. Header removal and exit landing use `l_move` with explicit overlapping byte intervals and one top adjustment; they cannot be implemented by repeating a construction or by releasing below live escape bytes.

A plain alternate return needs no TLS target record. Low code saves the current top as the replacement start, constructs there through this function's existing result stack/count channels, and retains its incoming original start in frame address storage. After completion it invalidates the bound named-local metadata/ownership, records abandonment without releasing across the replacement `[start,end)` interval, moves that interval to the incoming start with `l_move`, and updates top/prefix/count before the ordinary `t_ret []` epilogue. It neither loads a target cell nor changes the return discriminant. A direct named return only writes its current metadata to the existing output channels.

Dynamic byte stdout is `l_out_bytes`, a closed length-based runtime operation accepting an address and byte count; it does not reuse `l_rt out_text`, whose literal-text field cannot represent a dynamic run. For one `print`, lowering reserves a statement-owned line buffer and evaluates/renders operands into it in order: `pa_view` of `u8` copies exactly its sampled byte run, text literals copy their exact bytes, and scalar/other-aggregate forms use `l_fmt`/literal-copy/iteration. Each earlier operand is rendered before a later operand can mutate its source. After every operand completes, one LF byte is appended and exactly one `l_out_bytes(buffer, total_count)` emits the joined line. Output produced while later operands evaluate precedes that whole line, as D-1 requires. An abort or escape in an operand emits no partial outer line. The buffer stays live through emission and is released afterward; embedded NUL and non-UTF-8 bytes are copied and counted unchanged. Low `GIR-V090` checks the output interval/lifetime and `GIR-V100` its origin. Native stdout-byte comparison uses raw files, not C strings or Unicode-normalized text.

The C emitter implements `l_fmt` with the closed integer/unsigned/bool text-formatting helpers, returning the byte count; raw byte views use `l_copy`. Its inherited `l_rt` signature and output entry points remain unchanged. Structural rendering compiles recursively to literal bytes, scalar formatting and sampled-element CFG loops. These operations implement language text conversion, never an opaque constructor. Low `GIR-V090` checks primitive layouts, ABI component counts, target-cell bounds/types, every active-target save/restore path, discriminant branches, protected byte intervals and stack ownership before emission; `GIR-V100` retains origins for checks. This contract is required before `G-CONSTRUCT` can be reached; no low-level portion is implicitly parked by specifying the high protocol.

### 12.11 Construction trace and CLI result encoding

The abstract evaluator result in §4.5 carries both stdout bytes and the construction event list. The existing `run` and `gir-run` commands select their output shape from the input module profile. For `core-pilot` and `core-shrink`, their current JSON output bytes are unchanged. For `core-construction` the successful/fuel-limited encodings are `['done', Outcome, [byte], [Event]]` and `['timeout', [byte], [Event]]` (single quotes here stand for JSON double quotes); status is respectively 0 or 3. `Outcome` keeps the current `returned`, `aborted kind line`, and `exited code` records. Stdout is a byte list, each integer 0..255, so raw non-UTF-8 text is preserved. `fault kind` (status 4), `malformed message` (2), `rejected rule message` (5) and validation `ok` (0) retain their current records. A fault is not a successful construction observation. Exactly one compact JSON line is written.

Event records are `['begin', d]`, `['write', d, index]`, `['publish', d]`, `['copy', Source, d]`, `['relocate', d, Reason]`, `['stage', d, 'capacity-check']` and `['abandon', d]`. `d`/`index` are `nat`; `Reason` is `header-removal` or `exit-value`. `Source` is `['storage', storage_id, [nat] path]` or `['repeat', d]` for a fill's completed source. Storage ids are numbered by dynamic object creation order (globals in initialization order, then parameter/local objects in declaration/evaluation order); A private capacity-check stage is a compiler-created local object. Its storage id is allocated when `stage(d, capacity-check)` executes. Successful fit emits `copy([storage, stage_storage_id, []], d)` after the complete result passes the capacity check. Staging retains `d` and emits no second `begin`. For a slice-valued copy source, the storage id and path identify its logical descriptor object; the copied bytes come from its sampled backing storage. GIR sampling retains that descriptor provenance, including when the backing storage is static. Direct static literals initialize through writes and need no ordinary-copy source id. Destination ids are numbered by dynamic `begin` order and retained across calls, ownership transfer, staging and relocation. A named local bound to an incoming destination does not open a second trace destination. An element write uses its zero-based ordinal within the constructed array/run. Cancellation acknowledgement has no event.

Construction goldens may add `NAME.construct.json` containing `['construction', [Event]]`; `NAME.out` remains literal output bytes and `NAME.expect.json` remains the outcome expectation. A conformance case claiming a construction rule MUST include the event expectation, compare Core/GIR-H/native observations, and exercise a mutant that violates its named rule. Native `--trace-construction PATH` writes that same construction record to a requested artifact after execution (including abort/exit trace prefixes), never to program stdout; it is opt-in and its file errors fail loudly. `l_event` supplies the semantic marker; the native recorder assigns dynamic ids using the same begin/object order instead of serializing addresses. Trace-only scratch/instrumentation changes cannot be claimed as default-backend parity.

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

Classes are the coarsest partition of the instances that is **stable**: two instances are in one class only if their signatures are equal and their bodies are equal once each callee is replaced by its class. It is computed by refinement: start with instances grouped by signature, split any class whose members' bodies differ under the current classes, and repeat until nothing splits. The result does not depend on creation order, and it handles self-recursion and mutual recursion without a special case: two recursive groups merge exactly when their members correspond pairwise. A stable partition is precisely the premise of the sharing theorem (validation plan `TH-SHARE-01`).

A reference from a body to anything that is per-instance and not itself merged — a helper, a thunk, a channel — is part of the body's text, which keeps such instances distinct.

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

Sharing reduces emitted bodies. It does not reduce the number of contexts checked, and so does not reduce frontend cost (a). Reducing checking work needs the checker to check a body once against root parameters and each call site against the result — the structure of Core's `validate` (§4.6), which the Lean safety theorem shows sound for `core-pilot`, the only profile the Lean model covers so far. Applying that structure to the production checker is deferred (campaign, deferral `X1`).

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
