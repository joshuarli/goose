import Goose.Lower.Validation.SourceCanonicalRootFloorsSeeds
import Goose.Lower.Validation.ReplacementContentFlowSourceNativeContinuation
import Goose.Lower.Validation.FreshRunSource

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem native_definition_bounded {func : Func}
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    {block : GIR.Block} (member : block ∈ func.blocks.toList) {value : ValueId} {op : Op}
    (definition : Inst.def value op ∈ block.insts) : value < func.numValues := by
  apply List.mem_range.mp
  apply dense.mem_iff.mp
  apply List.mem_flatMap.mpr
  refine ⟨block, member, ?_⟩
  simp only [GIR.Block.defs, List.mem_append, List.mem_filterMap]
  exact Or.inr ⟨.def value op, definition, rfl⟩

theorem emitted_definition_native {env : LEnv} {before after : LS} {op : Op}
    {value : ValueId} {func : Func} (generated : GeneratedBuilderState before)
    (run : emitDef op env before = (value, after)) (live : after.cur.isSome = true)
    (continuation : NativeBuilderContinuation func after) :
    ∃ block ∈ func.blocks.toList, Inst.def value op ∈ block.insts := by
  have beforeLive := (dead_emitDef op).live_before run live
  cases current : before.cur with
  | none => simp [current] at beforeLive
  | some block =>
      obtain ⟨completed, extension, blocks⟩ := continuation
      exact emitted_definition_retained current (generated.live block current) run extension blocks

theorem emitted_static_canonical_floor {env : LEnv} {before after : LS} {op : Op}
    {value : ValueId} {func : Func} (generated : GeneratedBuilderState before)
    (run : emitDef op env before = (value, after)) (live : after.cur.isSome = true)
    (continuation : NativeBuilderContinuation func after) (bounded : value < func.numValues)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat)
    {root : RootRef}
    (produced : ∀ provenance, root ∈ rootsOfDef results types func provenance value op) :
    root ∈ rootsAt (func.provenance results types rootCount).vals value := by
  obtain ⟨block, member, definition⟩ := emitted_definition_native generated run live continuation
  exact provenance_static_definition results types func rootCount member definition produced bounded

theorem lowerPlace_var_canonical_floor {env : LEnv} {before after : LS}
    {slot : VarId} {value : ValueId} {func : Func} (generated : GeneratedBuilderState before)
    (run : lowerPlace (.var slot) env before = (value, after)) (live : after.cur.isSome = true)
    (continuation : NativeBuilderContinuation func after) (bounded : value < func.numValues)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    RootRef.local slot ∈ rootsAt (func.provenance results types rootCount).vals value := by
  apply emitted_static_canonical_floor generated run live continuation bounded results types rootCount
  intro provenance
  simp [rootsOfDef]

theorem lowerPlace_global_canonical_floor {env : LEnv} {before after : LS}
    {global : GlobalId} {value : ValueId} {func : Func} (generated : GeneratedBuilderState before)
    (run : lowerPlace (.global global) env before = (value, after)) (live : after.cur.isSome = true)
    (continuation : NativeBuilderContinuation func after) (bounded : value < func.numValues)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    RootRef.global global ∈ rootsAt (func.provenance results types rootCount).vals value := by
  apply emitted_static_canonical_floor generated run live continuation bounded results types rootCount
  intro provenance
  simp [rootsOfDef]

end Goose.Lower.Validation.SourceCanonicalRootFloors
