# Provisional Goose IR specification

**Revision:** GIR 0.1, 2026-10-12.  
**Status:** design proposal, not an implemented language or a completed formalization.  
**Repository baseline:** `62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a`.  
**Companions:** [campaign](goose-ir-campaign.md), [proof and validation plan](goose-ir-validation.md).

“MUST” and “MUST NOT” state the proposed contract for an implementation of this revision. They do not assert that the current compiler or a hypothetical future implementation already satisfies it. The current [Goose language specification](../goose_spec.md) takes precedence; a conflict requires a reviewed semantic decision and revision of this draft.

## 1. Purpose and representation boundaries

GIR preserves the facts that distinguish Goose long enough to analyze, validate, and lower them deliberately: typed storage, reference roots, stable growth, sampled views, construction destinations, effects, and scope-crossing exits. It is not textual C with different punctuation, a machine instruction set, or a second source-language typechecker.

There are three named representations:

| Representation | Purpose | What remains explicit |
|---|---|---|
| **Typed Goose Core** | Source-side semantics after resolution and concrete specialization. Structured, typed, unoptimized. | Source evaluation order, binding versus value access, scopes, construction contexts, source exit targets, root/effect obligations. |
| **GIR-H** | High-stage typed CFG for language-aware transformations. | Scalar SSA, explicit storage places, snapshots, construction and exit capabilities, logical roots, checked operations. |
| **GIR-L** | Low-stage CFG ready for a C or LLVM emitter. | Concrete layouts, runtime operations, explicit cleanup and call conventions, truthful alignment, source origins, retained evidence links. |

GIR-H and GIR-L share identifiers, CFG/value infrastructure, origins, and validation tooling. Stage legality is explicit; there are not two unrelated compiler frameworks. Each high operation has one semantics and a documented low expansion. Core remains distinct so that proving a GIR transform cannot conceal a faulty source-to-GIR translation.

Initially, memory effects are ordered by instruction order and control flow, not by an independently reorderable graph. There is no universal memory-SSA token in revision 0.1. Transformations must use the effect/invalidation contract before moving memory operations. Administrative construction and scope capabilities have separate path-linear checking.

## 2. Semantic profiles and supported subsets

Every artifact declares a semantic profile and feature set. Initial profiles are:

- `core-pilot`: integers/bools, fixed locals and elements, aliases, grow-only arrays, snapshot indexing/slicing, lexical scopes, branches/loops, restricted direct calls.
- `core-construction`: the pilot plus explicitly supported nonfixed construction, caller destinations, partial construction, and nonlocal exits.
- `gir-experimental`: a manifest of supported GIR features and lowering stages, expanded only with tests and decisions.

These are implementation-support profiles, not new source dialects. An unsupported operation is rejected by the experimental path with a feature-specific explanation. It is not translated to a generic opaque operation and counted as supported. Ordinary Goose checking and the legacy backend retain their existing language acceptance.

Globals, recursion, generics/function values, all ADT/array modes, pools, relative references, serialization, floats, threads, FFI, and native packages must each have independent implementation, model, proof, and test coverage entries. Full default-backend parity requires implementing them; the first model need not claim to prove them all.

## 3. Module contract and identities

A module contains:

```text
Module {
  schema_version,
  stage: Core | High | Low,
  semantic_profile,
  feature_manifest,
  numeric_profile,
  source_manifest,
  type_table,
  function_table,
  global_initialization_order,
  origins,
  entry_points,
  runtime_contract_version,
  target_layout?,
  evidence_manifest
}
```

`numeric_profile` separates release computation from debug instrumentation policy. `target_layout` is mandatory for GIR-L and representation-sensitive operations; abstract Core cases may omit it. The target record includes architecture/ABI identifier, pointer width, endianness, scalar alignment, stack reservation/size limits, and runtime layout identity. An LLVM target triple alone is not a full Goose runtime contract.

Use distinct ID domains: `SourceFileId`, `SourceNodeId`, `FunctionId`, `SpecializationId`, `TypeId`, `BlockId`, `ValueId`, `PlaceId`, `RootId`, `ScopeId`, `OriginId`, `TargetId`, and `EvidenceId`. Dense numbering is module-local and deterministic for identical inputs. Native addresses, hash-map iteration order, and AST allocation order are never serialized identities.

`SpecializationId` describes a compiled context. `FunctionId` identifies the source declaration. Neither is a dynamic invocation. Runtime semantics use a fresh **activation identity** for each invocation and scope entry where required, including recursive entries and loop-created locals.

`SourceNodeId` need not survive arbitrary edits. The linter's existing baseline/fingerprint algorithm, not a GIR ID, determines finding identity across line shifts. Origins connect generated operations to original source nodes plus specialization/inlining context; a synthesized operation records its responsible source construct and precision rather than inventing an exact span.

## 4. Typed Goose Core contract

Core is a typed structured language, not an export of the optimizer's mutable AST. Its node families include constants, explicit value reads, reference binding/rebinding, writes, scalar operations, sequencing, source conditionals/loops, calls, local/global declarations, array/view operations, construction expressions, explicit copies, ordinary returns, and nonlocal returns.

Frontend conveniences already resolved include overload selection, member-call receiver placement, concrete type arguments, implicit conversion choice, reference transparency, and source-name resolution. Core records the selected meaning. It does not redo overload resolution during execution.

Core MUST retain these distinctions:

- Reading a value versus retaining a reference or slice to mutable contents.
- Taking a receiver/extent snapshot versus reading the owner's current length later.
- Fresh construction versus copying existing storage versus the return of an eligible local.
- Source lexical lifetime root versus exact storage identity versus a conservative set of alternatives.
- A source failure versus a frontend rejection versus a malformed Core artifact.
- An ordinary return versus an exit targeting a particular active enclosing invocation.

A Core importer validates types, identifier references, definite initialization, supported lifetime obligations, and declared effect evidence. It cannot validate the parser/elaborator merely by checking their output is well-typed. That unproved boundary stays in the claim ledger.

## 5. Values, places, roots, and memory

### 5.1 Value types

The pilot uses `bool`, `i8/i16/i32/i64`, `u8/u16/u32/u64`, unit, and finite result tuples. Expanded profiles add `f32/f64`, nominal fixed values, ADT values, references, slices, and representation descriptors for nonfixed storage.

Signedness remains part of the type even if an implementation stores both signs as `BitVec w`. Operators choose signed interpretation explicitly. Metadata lengths and byte sizes use bounded, nonnegative size values; source `.len` remains the language-specified integer value. Conversions between source indices, byte sizes, and target addresses are explicit and checked where required. Release arithmetic wrap must never turn allocation-size overflow into an unchecked undersized allocation.

Fresh nonfixed values are not ordinary freely copyable SSA aggregates. They flow through destination/constructed-result capabilities. A reference or slice is an ordinary duplicable source value subject to Goose's lifetime/writability rules. No uniqueness is inferred from its safety.

### 5.2 Places and references

A `Place<T>` identifies typed storage. A `Ref<T>` identifies an accessible place plus the required reference form; a slice identifies an element run and a captured extent. Writability and whole-assignment permission are separate: Goose `let`, shallow `const`, and reference rebinding must not collapse into one immutable bit.

Logical memory records root instances, allocated subobjects, initialized ranges, value types, active scope ownership, committed extents, and pending construction ranges. The representation refinement later relates those to byte addresses and layouts.

A provenance descriptor contains a conservative alternative set, an exactness classification, lifetime bounds, storage reachability, writability, and applicable pool/grow-shrink properties. Unknown provenance is explicit. A lifetime root that bounds a target is not necessarily the exact allocation holding it. Joining alternatives cannot discard a possibility just to enable an optimization.

Physical region assignment is separate. Two logical roots may reuse a stack at disjoint lifetimes. Two references rooted at one owner may overlap or may denote distinct fields; neither relation follows solely from sharing a lifetime root. Distinct root labels alone are not a license for `noalias`.

### 5.3 Reclamation versus type-safe reuse

Actual scope reclamation or incompatible reuse invalidates references as the language requires. Logical removal from a limited array or freeing a reusable slot may leave an initialized same-typed value accessible through existing references. A global generation counter that invalidates all such references would describe the wrong language.

The model may use allocation generations to distinguish genuinely reclaimed storage, but MUST NOT introduce runtime generation checking or new source rejection for legal limited/reusable-slot references. Content identity can change while memory validity remains true. See the language's limited-array and reusable-pool clauses. [S1]

## 6. CFG and SSA form

A function contains an entry block, block table, parameter/result signature, source scope tree, effect summary, optional target bindings, and origin. Blocks have typed parameters, ordered instructions, and one terminator. Control-flow edges pass values explicitly; block parameters provide phi semantics.

Scalar SSA definitions dominate uses. Memory-resident variables use typed places and explicit reads/writes; address-taking does not pretend the stored value remains immutable SSA. Aggregate scalar replacement is a later optimization, not an assumption of the initial lowering.

Terminators are:

| Terminator | Contract |
|---|---|
| `br block(args)` | Unconditional edge; argument arity/types match. |
| `condbr condition, then(args), else(args)` | `bool` condition; exactly one successor executes. |
| `switch tag, cases, default` | Typed exhaustive or explicitly defaulted dispatch. |
| `ret results` | Return only after required local cleanup and result publication/transfer. |
| `invoke callee(args) normal block escape block` | Call with possible Goose nonlocal escape; both continuations are explicit. Not native exception handling. |
| `escape signal` | Propagate an administrative nonlocal-exit signal after appropriate local cleanup. |
| `abort reason, origin` | Defined terminal runtime failure, not undefined behavior. |
| `process_exit code` | Declared whole-program termination, where supported. |

A proven-impossible block may later use `unreachable` only with separately validated reachability evidence. It is not the default expansion of an unsupported feature, failed source check, or malformed runtime input. Revision 0.1 implementations may omit the opcode entirely.

Scope nesting is a separate metadata tree and verifier state, not arbitrary brace nesting inherited from C. Branches cannot jump into a scope without its required entry state or leave with live unhandled administrative resources.

## 7. Operation families and effects

The spellings below are proposed canonical operation names. Structured opcode/operand records are authoritative; the readable syntax in examples is explanatory until a parser/printer implementation and grammar tests are accepted.

| Family | Representative operations | Key contract |
|---|---|---|
| Pure scalar | `const`, `int.add.wrap`, `int.cmp`, `bool.not`, tuple projection | Exact typed value computation; no silent widening. |
| Profile arithmetic | `int.add.signed`, `int.div.goose`, `int.mod.euclid`, `int.shift.masked`, `num.cast` | Profile-specific defined behavior and failures. |
| Storage | `place.local`, `place.field`, `ref.make`, `value.load`, `value.store`, `ref.rebind` | Explicit typed access and initialization; aliases allowed. |
| Copies | `value.copy`, `bytes.move` | Respect source copy permission and overlapping-copy semantics; not interchangeable with fresh construction. |
| Views | `array.snapshot`, `slice.snapshot`, `slice.make`, `array.index.checked` | Preserve receiver and extent sampling order. |
| Arrays | `array.push_value`, `array.resize`, `array.clear`, `array.length` | Explicit owner/effect and source legality; no invented bounds exemptions. |
| Construction | `dest.acquire`, `construct.begin`, `construct.field`, `construct.call`, `construct.finish`, `construct.abandon` | Path-linear receiving-storage protocol with operation-specific publication. |
| Scopes | `scope.enter`, `scope.leave`, low-stage watermark operations | Balanced lifetime/cleanup ownership on every relevant path. |
| Exits | `target.enter`, `target.match`, `target.finish`, `exit.make` | Dynamic invocation identity and result-destination ownership. |
| Representation | `layout.offset`, `packed.load`, `packed.store`, `relative.decode`, `relative.encode` | Stage/profile restrictions and explicit layout/refinement obligations. |
| External | `runtime.call`, `extern.call`, later queue/thread operations | Versioned contracts and conservative effects; unsupported interfaces are not treated as pure. |

An effect summary records, relative to parameters/globals/captures: read/write locations; growth/shrink/clear; reference/holder rebinding; allocation/construction interactions; potential abort; possible nonlocal targets; external I/O; escape/capture; and unknown effects. Distinguish an element write from changing an array extent or retargeting a reference variable.

Summaries are derived from bodies or checked against trusted runtime contracts. Recursive summaries converge through a conservative fixpoint. Failure to reach the planned precision widens to unknown; it never yields an empty effect set. A serialized summary claiming fewer effects than its implementation has fails validation or is excluded from an implementation-proved claim.

A call is not speculatable merely because its result is unused. Potential abort, nonlocal return, mutation, input/output, or unknown behavior forbids treating it as effect-free. Contract facts used by the linter remain independently classified from optimization permissions.

## 8. Numeric and failure semantics

### 8.1 Integer table

The following reflects the inspected language clauses, not conventional C defaults. [S2]

| Source behavior | GIR rule |
|---|---|
| Exact-width arithmetic | Operands arrive at the resolved common type; no backend promotions are semantic. |
| Unsigned add/sub/mul | Modulo `2^w` in every build. |
| Signed add/sub/mul/neg | Defined two's-complement wrap in release; debug instrumentation checks executing operations under the policy below. |
| Division by zero | Mandatory abort in every profile. |
| Signed division | Truncating signed quotient except the explicit overflow cases; validate against source fixtures. |
| `i64.min / -1` | Mandatory abort, including release. |
| Narrower signed minimum / -1 | Debug overflow failure; release wraps at that width. |
| Integer `%` | Euclidean remainder in `[0, abs(divisor))`; zero divisor aborts; signed minimum `% -1` is zero. |
| Shifts | Mask count to `0..w-1`; signed right shift sign-extends, unsigned right shift zero-extends. |
| `as` integer conversion | Debug range check; release width/sign conversion as specified. |
| `as!` integer conversion | Unchecked width/sign conversion even in debug. |

The signed-minimum Euclidean remainder implementation must not compute `abs(min)` in an overflowing same-width signed intermediate. Lean may use mathematical integers internally with a proved correspondence; the emitted code needs a safe finite-width expansion.

`BitVec` library functions are not Goose semantics by themselves. Wrap total library operations with Goose's required failures, particularly zero division. [E1]

### 8.2 Debug instrumentation

The source spec permits optimization to regroup or remove signed-overflow-checked operations; debug checks attach to operations that actually execute. Therefore release semantic preservation and exact source-debug trace equality are different obligations. [S2]

Use these contracts:

- The reference `debug-unoptimized` profile checks source Core operations as executed without optimizing them.
- Mandatory failures remain mandatory in every optimization profile.
- A transform must preserve release behavior. Its actual optimized GIR arithmetic receives the required debug instrumentation for the operations retained.
- Debug cast checks or other checks do not acquire signed-arithmetic latitude merely because they are debug-only. Their transformation rules need separate justification.
- Optimized-debug tests compare exact behavior only where the spec requires it; otherwise compare the approved instrumentation policy and record the distinction.

A backend may initially preserve more source-operation structure to simplify debug checking. That is an implementation choice, not a new universal promise that all future optimizers reproduce every source intermediate failure.

### 8.3 Floats

Represent widths and conversion points explicitly. No default fast-math permissions. Structural equality must respect float semantics, including signed zero and NaN, rather than indiscriminate byte comparison. Full IEEE/rounding behavior is deferred from the pilot, not silently approximated with mathematical reals.

The conversion profile must include the current finite out-of-range float-to-int wrapping rule and NaN-to-zero rule, and adjudicate infinity/rounding/environment edge cases before claiming full coverage. `as` versus `as!` and conversion-to-float exceptions retain source meaning. Direct LLVM float-to-int instructions cannot stand in for a defined out-of-range conversion without a correct expansion. [S3]

### 8.4 Outcome classes

Separate `Return`, defined `Abort`, explicit process exit, divergence, and external-interaction traces from `RejectedSource`, `MalformedArtifact`, `UnsupportedFeature`, and harness `Inconclusive`. A malformed module is a compiler/tool error, not a new Goose runtime behavior. Runtime abort need not run ordinary scope cleanup; it terminates the program unless the source contract explicitly says otherwise.

## 9. Evaluation order and view snapshots

`array.snapshot(owner)` samples the selected region/receiver and current extent before evaluating an index or slice-bound expression. A snapshot is not a copy of elements and not a promise that the owner remains unmodified. It retains the source view and the lifetime obligation needed to access it.

`array.index.checked(snapshot, i)` checks `0 <= i < snapshot.length` and returns a typed element reference. It MUST NOT resample the owner's current length. A later pure growth can preserve access to an old element but cannot retroactively enlarge this sampled bound. Rebinding the variable originally used to name the owner does not retarget the snapshot.

Example, using schematic source operations:

```text
items = [7]
x = items[append_one_and_return_index(items)]
```

If the index function appends one element and returns index 1, indexing fails against the sampled extent 1 even though `items.length` is now 2. The index function executes once. Its permitted prior effect is not undone by the later failure.

Proposed high-stage expansion:

```text
%s = array.snapshot %items                 : Snapshot<i32>
%i = call @append_one_and_return_index(%items) : i64
%p = array.index.checked %s, %i             : Ref<i32>  origin O_index
%x = value.load %p                         : i32
```

`%s` carries the original receiver, captured length, and lifetime relationship. Effect validation checks that the call may grow but cannot invalidate the sampled storage. `call` in this example is the ordinary instruction form for a callee with no nonlocal escape; a possibly escaping callee uses `invoke`.

Ordinary source `for` semantics require care: a counted integer loop's bound can be sampled, while array iteration may reread the array length as the language specifies. Never apply the snapshot-index rule as a blanket rule that every loop freezes length. Explicit Core loop kinds preserve this distinction. [S1]

Assignments resolve their destination first. Compound assignments also load the old value before RHS evaluation. Whole-resizable assignment instead performs its source-defined clear-before-construction, with the static prohibition on forbidden RHS access. These are separate Core/GIR forms, not one generic store rewrite.

## 10. Proof witnesses and check elimination

A checked index operation may be split into a guard and an access:

```text
%w = bounds.guard %snapshot, %index   : BoundsWitness
%p = array.index.proven %snapshot, %index, %w : Ref<T>
```

A witness proves a predicate about the exact SSA index, sampled extent, and relevant storage state. It is not a user Boolean. The guard's successful edge establishes the predicate. A static-analysis witness is accepted only after a checker validates its derivation from the actual CFG, numeric facts, and effects.

Growth may preserve storage-validity facts and selected length inequalities. Shrink, clear, retargeting, reference-field mutation, unknown calls, or arithmetic wrap may invalidate different facts. The witness format MUST distinguish the sampled numerical bound from the continued validity of the referenced storage. Satisfying one does not imply the other.

A BCE certificate identifies the subject function/profile/version, instruction and operands, domination context, fact derivation, numeric widths, and effect path. Content hashes detect stale association; they are not semantic proof. The checker reads the actual module, reconstructs the claimed premises, and validates the inference. An unconditional `assume(in_bounds)` is not an acceptable certificate.

Checked witnesses may be erased for code generation only after validation. Evidence may be invalidated by transforms; a pass either transports it through a justified mapping, rechecks it, or restores the runtime check. Keep an audit record for removed checks in debug/compiler-testing builds.

## 11. Scopes, regions, and construction

### 11.1 Scope resources

`scope.enter` creates a dynamic scope instance and administrative ownership of local storage. GIR-H refers to logical roots. GIR-L introduces concrete watermarks and runtime stack operations. Normal fallthrough, break, continue, ordinary return, and nonlocal propagation each perform the cleanup required by the scopes they actually leave.

A scope capability is not a source value: it cannot be stored in a Goose array, copied into a closure as ordinary data, forged, or returned accidentally. At a CFG branch it may be forwarded to mutually exclusive successors; on each actual path it is consumed or transferred exactly as required. Loop re-entry creates fresh dynamic instances. Valid transfers across backedges must be explicit and checked.

Only reclaimed local roots are reset. Caller-owned receiving storage, globals, and surviving references are not reclaimed merely because a callee exits. Stack sharing needs a validated lifetime/placement plan, not equality of static scope numbers.

### 11.2 Receiving destinations

A destination descriptor contains:

```text
Destination {
  receiving_owner,
  element_or_field_path,
  result_type,
  construction_mode,
  capacity_policy,
  publication_policy,
  caller_lifetime,
  layout_policy
}
```

Modes distinguish fresh local/global construction, caller result construction, element/field construction, explicit copy, returned-local transfer, and bounded staging. An initializer's result is not materialized into arbitrary temporary storage simply because it passes through a call or branch.

`dest.acquire` and `construct.begin` create administrative construction state. `construct.field`/`construct.call` transfer or temporarily delegate the relevant receiving range. `construct.finish` publishes the completed result according to the operation's contract. `construct.abandon` disposes of only the incomplete portion it owns and performs the specified restoration. Every normal/nonlocal path accounts for these resources. Terminal program abort is a separate outcome.

These capabilities express compiler obligations, not source exclusivity over every reference into the containing array. Existing initialized elements may remain readable/writable where Goose permits it. Prohibition of growth during construction applies to the precise source cases, including fresh nonfixed/relative-bearing construction, not to an invented rule rejecting all nested fixed-value push arguments.

For example, `array.push_value` accepts an already evaluated, copy-permitted fixed value and performs its source-defined push. A nonfixed constructor or relative-bearing fresh value uses receiving-storage construction, with the corresponding growth restrictions. The lowering must preserve the source evaluation/commit order of each form.

### 11.3 In-place contract and permitted movement

The resource trace distinguishes `FreshDestination`, `WriteInit`, `Publish`, `ExplicitCopy`, `MoveWithinDestination`, `BoundedStage`, and `Abandon`. These are semantic instrumentation events, not exact machine instruction counts.

Allowed internal movements include the source-specified packed-prefix or delivered-header layout changes. They must preserve final representation, evaluation order, and reference targets. The implementation must prove either that no exposed address is invalidated or that the permitted representation transformation correctly adjusts every affected link. A logical model that magically updates all references is not a byte-level correctness proof.

Bounded-receiver staging requires an explicit reason: the full result extent is unavailable before evaluation and capacity must be established before writing outside the receiver. It does not authorize staging ordinary fresh results for growable receivers. Initializers execute once.

Returned locals and exits abandoning partial destinations use the exact return/construction rules; `return local` is not silently modeled as a free move in every case. Freeze their decision table before implementing that feature.

**Construction is not a universal transaction.** Earlier external side effects or completed elements are not rolled back automatically. An append may publish completed elements incrementally where specified. Restoration concerns only the incomplete destination range and scope resources the current operation owns. The publication/abandonment rule is part of each operation's semantics and validation tests. [S4]

## 12. Calls and nonlocal returns

Ordinary `call` is legal when the callee has no possible Goose nonlocal escape at that site. A call may still perform declared I/O/mutation or terminate by abort. `invoke` is required when a nonlocal escape can occur.

A target-bearing function invocation creates a hidden activation-bound target capability associated with its result signature and destination. Statically resolved `return ... from f` selects the correct dynamically active invocation under Goose's rules. A source function ID alone is insufficient in recursive/nested cases. Target capabilities are internal control objects, not user first-class continuations.

An escape signal contains the target capability, result discriminant, fixed result payload or completed destination handle, and only the administrative transfer state required to preserve the result. It is consumed by a matching catch or forwarded after local cleanup. It cannot be duplicated, arbitrarily stored, or handled by an unrelated same-named function.

Proposed CFG shape:

```text
^entry:
  %scope = scope.enter S_caller
  %target = target.enter @caller, %caller_result_destination
  invoke @worker(%args, %target)
      normal ^normal(%value)
      escape ^unwind(%signal)

^normal(%value):
  ... construct/publish normal result ...
  scope.leave %scope
  target.finish %target
  ret %normal_result

^unwind(%signal):
  ... abandon only incomplete local construction ...
  ... leave scopes between this site and the selected target ...
  %mine = target.match %signal, %target
  condbr %mine, ^catch(%signal), ^propagate(%signal)

^catch(%signal):
  ... consume signal and preserve caller-owned result storage ...
  ... discharge remaining resources of this invocation ...
  ret %signal_result

^propagate(%signal):
  ... discharge remaining resources owned by this invocation ...
  escape %signal
```

Ellipses are required expansions, not executable syntax or permission to omit cleanup. The verifier tracks target/scope/resource state along each edge; a production module cannot contain these ellipses. The escape edge is not assumed to mean all scopes have already been cleaned.

GIR-L may initially lower this to the existing `gs_rf`/thread-local channel implementation, whose details remain backend/runtime choices. A different explicit-result convention requires its own equivalence argument and measurements. The high-stage contract neither requires an unwinder nor promises zero-cost nonlocal returns. [S5]

## 13. Layout, relative references, and low-stage legality

### 13.1 Layout descriptors

Every representation-sensitive type has a descriptor: fixed/variable/resizable class, nominal identity, packed field order, explicit padding, header/length encoding, element traversal, ADT mode/tag mapping, and actual alignment. Variable-size fields use checked offset computations; a C `sizeof` assumption cannot replace a dynamic layout rule.

GIR-L describes physical reference forms separately from logical `Ref<T>`: plain address, resizable header-plus-stack form, pool reference with freelist context, and slices. Hidden parameters are explicit in low-stage signatures. Runtime layout/version and internal ABI compatibility are verified across modules and wrappers. [S5]

Raw byte operations appear only with a typed layout/initialization justification or a defined runtime contract. Loads use the alignment actually guaranteed; packed storage normally cannot inherit natural scalar alignment. Memory-copy overlap is explicit, and a copy's permission/extent is checked before choosing `memcpy` versus `memmove`-style lowering.

### 13.2 Relative references

`relative.decode` turns an encoded storage link into a plain logical reference. `relative.encode` stores a target using the field's exact self-relative or named-pool scheme, null convention, width, and required checks. Pool identity is part of the type contract where specified. A relative storage slot is not treated as an ordinary integer with arbitrary arithmetic. [S6]

Link correctness requires both lifetime/provenance and byte-offset representability. Moving a self-relative aggregate is legal only under the source's copy/relocation rules. A nominal type tag alone does not prove that every encoded offset names a correctly typed initialized target. Serialization validation is a separate refinement feature.

### 13.3 GIR-L operation requirements

After storage/exit lowering, no unresolved source overloads, abstract construction destinations, implicit scope exits, generic placeholders, or uninterpreted relative-link encodings may remain. Each low operation has explicit sizes, alignment, destination lifetime, runtime ABI, and failure behavior.

The emitter may reuse current C runtime helpers without embedding their bodies in the IR. Each helper call names a contract and implementation version. Testing a helper is not proving it; the trust ledger records its status. Do not replace Goose data stacks with native `alloca` merely because both are called stacks.

## 14. Backend obligations

### C

Emit statements/temporaries in semantic order instead of relying on C argument evaluation order. Implement release wrapping without C signed-overflow undefined behavior. Respect aliasing, alignment, packed layout, overlap, and foreign ABI boundaries. Preserve existing runtime diagnostics and source mapping where required. A real GIR backend consumes GIR-L directly; reconstructing the old AST is not migration completion.

Keep C wrappers for foreign aggregate conventions and retain the existing runtime/toolchain path. Backend-local helpers may choose an efficient implementation after semantic obligations are met. Reformatting all generated C or changing global symbol naming is not an independent success metric.

### LLVM, optional later stage

Use ordinary supported LLVM IR and a pinned data layout. Never infer `noalias` from Goose reference safety; never attach `nsw`, `nuw`, `inbounds`, `nonnull`, `dereferenceable`, alignment, or lifetime claims without their exact preconditions. Preserve explicit mandatory checks before instructions whose exceptional operands would invoke undefined behavior or poison. In particular, wrapping add is not checked `add nsw`, and defined out-of-range conversions need an expansion. LLVM well-formedness verification does not prove Goose semantic preservation. [E2]

Use conservative attributes initially. Runtime and FFI wrappers can remain C. Compare emitted LLVM against Clang output from the same GIR/C computation and against real workloads before claiming an advantage. [E3]

## 15. Verifier contract

The C++ verifier runs after import and every mutating pass in testing/validation modes. Release pipelines may reduce repeated checks only after an explicit performance decision; never skip required untrusted-artifact validation. A Lean verifier for selected profiles is independent evidence with its own correspondence theorem.

| Code family | Required checks |
|---|---|
| `GIR-V001` module | Versions, supported features, entry points, complete symbols, closed schemas, resource bounds. |
| `GIR-V010` types | Concrete types, legal operand/result combinations, resolved widths, result arity, no unfinished type graphs. |
| `GIR-V020` CFG | Terminators, edge arity/types, dominance, scope-entry legality, loop resource state, reachable-definition consistency. |
| `GIR-V030` storage | Definite initialization, field/element layout, valid place formation, writable access, source copy permissions. |
| `GIR-V040` provenance | Sound alternative sets, lifetime bounds, exactness, possible aliasing, supported shrink/reuse distinctions. |
| `GIR-V050` effects | Calls respect conservative summaries, unknown effects remain unknown, invalidations applied, recursion handled. |
| `GIR-V060` construction | Correct receiving owner, single-path resource accounting, publication/abandonment, no unauthorized staging/reentrant growth. |
| `GIR-V070` exits | Target activation/scope relationships, exact result shape, cleanup of exited scopes, survival of transferred destinations. |
| `GIR-V080` evidence | Subject association, domination, numeric side conditions, mutation invalidation, no forged proof/assumption flags. |
| `GIR-V090` stage/layout | High/low opcode legality, actual alignment, size checks, runtime/target compatibility, resolved hidden ABI. |
| `GIR-V100` origins | Valid source mappings and honest precision; source identity independent of codegen numbering. |

These codes name compiler/tool diagnostics, not new user lint rule IDs. A verifier that only checks SSA and types MUST NOT advertise the complete storage/effect contract. Unsupported proof/validation obligations cause explicit rejection or a weaker claim level, not invented evidence.

The verifier is not a sandbox for executing arbitrary native programs. Verification and conformance tooling never automatically run untrusted imported code merely because its IR parses.

## 16. Serialization, evolution, and caching

Use a deterministic, bounded structured JSON representation initially; a human-readable GIR dump is a separate view. Encode wide integers and bit patterns as canonical strings, not JSON floating numbers. Specify duplicate/unknown-field rejection, maximum module/record/table sizes, nesting depth, and operation-count limits. The first importer accepts only the exact profile/schema it implements. Canonicalization order and source encoding are tested.

Version separately: surface semantic profile, Core/GIR schema, runtime/layout ABI, certificate format, and lint facts/diagnostics. A schema version does not imply proof coverage. Unknown mandatory capabilities fail closed. If adding an optional field to a closed schema, bump the corresponding version and update both sides deliberately.

Cache keys include canonical program/source/resource identity, imported module identities, entry points, frontend options, semantic/numeric profile, target layout, runtime ABI, compiler build identity, pass pipeline, schema, and evidence/checker version where applicable. The current lint runtime-version field alone is insufficient. Hashes associate artifacts; structural/semantic checks still validate claims. No cached verdict survives a change to assumptions without revalidation.

Lint facts remain their current private JSONL protocol. Do not replace them with GIR serialization or append new fields to v1 silently. The linter requires original statements/comments/call-use shapes that optimized GIR may no longer contain. [S7]

## 17. Transformation preservation obligations

For the deterministic closed pilot, a successful compilation must preserve return/mandatory-abort/external trace behavior under the same environment and profile. For divergence, state a separate simulation/productivity result rather than relying only on terminating runs. Later nondeterministic external/concurrent profiles require a reviewed refinement relation; do not impose single-trace equality on them accidentally.

Use a state relation between Core memory/control and GIR memory/control, allowing administrative stuttering. A decreasing rank or other progress argument prevents an infinite target-only administrative loop from being waved away as stuttering. Resource events are compared under the approved construction contract, not simply erased along with all internal operations.

Each pass supplies a manifest: supported opcodes, preconditions, preserved invariants, effect-summary changes, evidence transport, origin mapping, failure behavior, and tested/proved status. Removing a required aborting operation because its value is dead is forbidden. Moving a load across an aliasing write or a snapshot across a mutating argument requires a real proof of equivalence.

A theorem about a Lean pass proves that Lean pass. The production C++ path needs verified reuse/correspondence or a checked-instance connection for stronger claims. Otherwise label it model-proved plus differential-tested. Keeping this distinction explicit is part of GIR's design, not a documentation afterthought.

## 18. Provisional decisions and closure conditions

| Decision | Proposed default | Required closure evidence |
|---|---|---|
| IR infrastructure | Small custom typed CFG; no initial MLIR dependency | Working parser/verifier/lowering and measured maintainability; framework adoption needs separate justification. |
| Memory ordering | Ordered instructions and conservative effects | Sound motion/invalidation tests; add memory SSA only for a demonstrated need. |
| Administrative resources | Path-linear capabilities, erased after validation | Loop/branch/escape validator and semantic correspondence. |
| Alias abstraction | Reuse current root-set work, distinguish bounds/exact identity | Reconcile current code, lattice laws, alias witnesses, call-fixpoint tests. |
| Nonlocal target implementation | Dynamic activation capability in semantics; current runtime protocol initially | Recursive/nested target fixtures and destination/cleanup simulation. |
| Byte layout | Existing runtime layout first | Abstract-to-byte refinement cases and ABI tests. |
| Debug policy | Release preservation plus spec-conforming executing-operation instrumentation | Numeric decision ledger and profile-aware tests. |
| Runtime exhaustion | Explicit finite capacity/outcome or stated capacity precondition | Overflow/guard behavior mapped to actual runtime contract. |
| Floats/threads/FFI | Explicitly deferred from pilot | Separate profiles; no silent opaque implementation counted as proof. |
| Promotion | Opt-in until product parity | Campaign G7; no automatic default switch. |

## References

Pinned Goose sources:

[S1]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/goose_spec.md
[S2]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/goose_spec.md#62-integer-semantics
[S3]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/goose_spec.md#63-conversions
[S4]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/goose_spec.md#43-the-in-place-construction-guarantee
[S5]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/src/codegen.h
[S6]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/design/relative_references.md
[S7]: https://github.com/joshuarli/goose/blob/62366eb45fadeb2d0be1d840ff0c43c5c2cebf0a/docs/lint/facts-v1.md

External primary references, consulted 2026-10-12:

- **E1:** [Lean bitvectors](https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/).
- **E2:** [LLVM language reference](https://llvm.org/docs/LangRef.html) and [undefined behavior manual](https://llvm.org/docs/UndefinedBehavior.html).
- **E3:** [LLVM frontend performance guidance](https://llvm.org/docs/Frontend/PerformanceTips.html).
