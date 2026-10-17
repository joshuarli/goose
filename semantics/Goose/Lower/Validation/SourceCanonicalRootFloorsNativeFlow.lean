import Goose.Lower.Validation.SourceCanonicalRootFloorsNativeDefinitions
import Goose.Lower.Validation.ReplacementClosure
import Goose.Lower.Validation.ProvenanceConvergenceFinite

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR ReplacementContentFlowSource ProvenanceConvergence

theorem emitted_forward_canonical_floor {env : LEnv} {before after : LS}
    {op : Op} {value input : ValueId} {func : Func}
    (generated : GeneratedBuilderState before) (run : emitDef op env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (bounded : value < func.numValues) (forward : RootForward op input)
    {results : Array (List RootRef)} {types : Array (Option VTy)} {rootUniverse : List RootRef}
    (universeBound : RootUniverse results func rootUniverse) (rootCount : Nat)
    (rootBound : rootUniverse.length ≤ rootCount) :
    rootsAt (func.provenance results types rootCount).vals input ⊆
      rootsAt (func.provenance results types rootCount).vals value := by
  obtain ⟨block, member, definition⟩ := emitted_definition_native generated run live continuation
  have closed := provenance_instructionRootsClosed (types := types) universeBound rootCount rootBound
  apply provenance_closed_forward closed member definition _ forward
  simpa only [(provenance_sizes results types func rootCount).2] using bounded

theorem emitted_load_local_canonical_floor {env : LEnv} {before after : LS}
    {value address : ValueId} {slot : SlotId} {func : Func}
    (generated : GeneratedBuilderState before)
    (run : emitDef (.load address) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (bounded : value < func.numValues)
    {results : Array (List RootRef)} {types : Array (Option VTy)} {rootUniverse : List RootRef}
    (universeBound : RootUniverse results func rootUniverse) (rootCount : Nat)
    (rootBound : rootUniverse.length ≤ rootCount) (reference : valRefLike types value = true)
    (addressRoot : RootRef.local slot ∈ rootsAt (func.provenance results types rootCount).vals address) :
    rootsAt (func.provenance results types rootCount).slots slot ⊆
      rootsAt (func.provenance results types rootCount).vals value := by
  obtain ⟨block, member, definition⟩ := emitted_definition_native generated run live continuation
  have closed := provenance_instructionRootsClosed (types := types) universeBound rootCount rootBound
  apply provenance_closed_load_local closed member definition _ reference addressRoot
  simpa only [(provenance_sizes results types func rootCount).2] using bounded

theorem emitted_load_local_seed_canonical_floor {env : LEnv} {before after : LS}
    {value address : ValueId} {slot : SlotId} {func : Func}
    (generated : GeneratedBuilderState before)
    (run : emitDef (.load address) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (bounded : value < func.numValues)
    {results : Array (List RootRef)} {types : Array (Option VTy)} {rootUniverse : List RootRef}
    (universeBound : RootUniverse results func rootUniverse) (rootCount : Nat)
    (rootBound : rootUniverse.length ≤ rootCount) (reference : valRefLike types value = true)
    (addressRoot : RootRef.local slot ∈ rootsAt (func.provenance results types rootCount).vals address) :
    rootsAt func.slotRootSeeds slot ⊆ rootsAt (func.provenance results types rootCount).vals value := by
  intro root seed
  exact emitted_load_local_canonical_floor generated run live continuation bounded universeBound
    rootCount rootBound reference addressRoot
    (canonical_slot_seed_floor results types func rootCount slot root seed)

theorem emitted_load_contents_canonical_floor {env : LEnv} {before after : LS}
    {value address : ValueId} {parameter : Nat} {func : Func}
    (generated : GeneratedBuilderState before)
    (run : emitDef (.load address) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (bounded : value < func.numValues)
    {results : Array (List RootRef)} {types : Array (Option VTy)} {rootUniverse : List RootRef}
    (universeBound : RootUniverse results func rootUniverse) (rootCount : Nat)
    (rootBound : rootUniverse.length ≤ rootCount) {mode : Mutability} {element formal : Ty}
    (typed : types[value]? = some (some (.data (.slice mode element))))
    (parameterAt : func.params[parameter]? = some formal) (reference : formal.isRefSlice = true)
    (addressRoot : RootRef.param parameter ∈ rootsAt (func.provenance results types rootCount).vals address) :
    ((func.roots.contents.find? (·.1 == parameter)).map (·.2)).getD [] ⊆
      rootsAt (func.provenance results types rootCount).vals value := by
  obtain ⟨block, member, definition⟩ := emitted_definition_native generated run live continuation
  have closed := provenance_instructionRootsClosed (types := types) universeBound rootCount rootBound
  have valueBound : value < (func.provenance results types rootCount).vals.size := by
    simpa only [(provenance_sizes results types func rootCount).2] using bounded
  intro root included
  apply closed.definition member definition valueBound
  simp only [rootsOfDef, valRefLike, typed, VTy.refLike, Ty.isRefLike, ite_true]
  apply Goose.Core.Sound.unionRoots_right
  exact List.mem_flatMap.mpr ⟨.param parameter, addressRoot, by
    simpa only [parameterAt, reference, ite_true] using included⟩

theorem emitted_call_argument_canonical_floor {env : LEnv} {before after : LS}
    {value input : ValueId} {callee : FnId} {args : List ValueId} {origin : Option OriginId}
    {func : Func} (generated : GeneratedBuilderState before)
    (run : emitDef (.call callee args origin) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (bounded : value < func.numValues)
    {results : Array (List RootRef)} {types : Array (Option VTy)} {rootUniverse : List RootRef}
    (universeBound : RootUniverse results func rootUniverse) (rootCount : Nat)
    (rootBound : rootUniverse.length ≤ rootCount) {parameter : Nat}
    (dependency : RootRef.param parameter ∈ rootsAt results callee) (argument : args[parameter]? = some input) :
    rootsAt (func.provenance results types rootCount).vals input ⊆
      rootsAt (func.provenance results types rootCount).vals value := by
  obtain ⟨block, member, definition⟩ := emitted_definition_native generated run live continuation
  have closed := provenance_instructionRootsClosed (types := types) universeBound rootCount rootBound
  have valueBound : value < (func.provenance results types rootCount).vals.size := by
    simpa only [(provenance_sizes results types func rootCount).2] using bounded
  intro root included
  apply closed.definition member definition valueBound
  simp only [rootsOfDef]
  exact List.mem_flatMap.mpr ⟨.param parameter, dependency, by simpa only [argument] using included⟩

theorem emitted_call_global_canonical_floor {env : LEnv} {before after : LS}
    {value : ValueId} {callee : FnId} {args : List ValueId} {origin : Option OriginId}
    {func : Func} (generated : GeneratedBuilderState before)
    (run : emitDef (.call callee args origin) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (bounded : value < func.numValues)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat)
    {global : GlobalId} (dependency : RootRef.global global ∈ rootsAt results callee) :
    RootRef.global global ∈ rootsAt (func.provenance results types rootCount).vals value := by
  apply emitted_static_canonical_floor generated run live continuation bounded results types rootCount
  intro provenance
  simp only [rootsOfDef]
  exact List.mem_flatMap.mpr ⟨.global global, dependency, by simp⟩

private theorem mapped_source_roots_subset (arguments : List (List RootRef))
    (declared initial target : List RootRef) (prior : initial ⊆ target)
    (parameters : ∀ parameter, RootRef.param parameter ∈ declared →
      (arguments[parameter]?.getD []) ⊆ target)
    (globals : ∀ global, RootRef.global global ∈ declared → RootRef.global global ∈ target) :
    declared.foldl (fun roots root => unionRoots roots (match root with
      | .param parameter => arguments[parameter]?.getD []
      | .global global => [.global global]
      | .local _ => [])) initial ⊆ target := by
  induction declared generalizing initial with
  | nil => exact prior
  | cons root rest ih =>
      apply ih
      · intro included member
        rcases Goose.Core.Sound.unionRoots_mem _ _ _ member with earlier | added
        · exact prior earlier
        · cases root with
          | param parameter => exact parameters parameter (by simp) added
          | global global =>
              have same : included = RootRef.global global := by simpa using added
              simpa only [same] using globals global (by simp)
          | «local» slot => simp at added
      · intro parameter member
        exact parameters parameter (by simp [member])
      · intro global member
        exact globals global (by simp [member])

theorem emitted_call_mapped_canonical_floor {env : LEnv} {before after : LS}
    {value : ValueId} {callee : FnId} {args : List ValueId} {origin : Option OriginId}
    {func : Func} (generated : GeneratedBuilderState before)
    (run : emitDef (.call callee args origin) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (bounded : value < func.numValues)
    {results : Array (List RootRef)} {types : Array (Option VTy)} {rootUniverse : List RootRef}
    (universeBound : RootUniverse results func rootUniverse) (rootCount : Nat)
    (rootBound : rootUniverse.length ≤ rootCount) (argumentRoots : List (List RootRef))
    (declared : List RootRef) (declarations : declared ⊆ rootsAt results callee)
    (arguments : ∀ (parameter : Nat) (roots : List RootRef), argumentRoots[parameter]? = some roots →
      ∃ input, args[parameter]? = some input ∧
        roots ⊆ rootsAt (func.provenance results types rootCount).vals input) :
    sourceMappedRoots argumentRoots declared ⊆
      rootsAt (func.provenance results types rootCount).vals value := by
  apply mapped_source_roots_subset argumentRoots declared [] _ (by simp)
  · intro parameter dependency root included
    cases present : argumentRoots[parameter]? with
    | none => simp only [present, Option.getD_none, List.not_mem_nil] at included
    | some roots =>
        obtain ⟨input, argument, floor⟩ := arguments parameter roots present
        apply emitted_call_argument_canonical_floor generated run live continuation bounded
          universeBound rootCount rootBound (declarations dependency) argument
        exact floor (by simpa only [present, Option.getD_some] using included)
  · intro global dependency
    exact emitted_call_global_canonical_floor generated run live continuation bounded results types
      rootCount (declarations dependency)

end Goose.Lower.Validation.SourceCanonicalRootFloors
