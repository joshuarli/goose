import Goose.Lower.Validation.ReplacementContentFlowSourceConsumedReferences
import Goose.Lower.Validation.ReplacementContentFlowSourceNativeContinuation
import Goose.Lower.Validation.FreshRunSource

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.GIR.ReplacementContentFlow.Model

theorem NativeBuilderContinuation.emitted_definition {func : Func} {env : LEnv}
    {before after : LS} {value : ValueId} {op : Op}
    (continuation : NativeBuilderContinuation func after)
    (run : emitDef op env before = (value, after))
    (live : before.cur.isSome = true) (generated : GeneratedBuilderState before) :
    ∃ block ∈ func.blocks.toList, Inst.def value op ∈ block.insts := by
  obtain ⟨completed, extension, blocks⟩ := continuation
  cases current : before.cur with
  | none => simp [current] at live
  | some block =>
    exact emitted_definition_retained current (generated.live block current) run extension blocks

theorem NativeBuilderContinuation.consumedBacking {env : PEnv} {root : DemandNode}
    {func : Func} {types : Array (Option VTy)} {upper : Prov} {le : LEnv}
    {before after : LS} {value source : ValueId} {op : Op} {sourceType : VTy}
    (continuation : NativeBuilderContinuation func after)
    (run : emitDef op le before = (value, after))
    (live : before.cur.isSome = true) (generated : GeneratedBuilderState before)
    (backing : BackingOp op source) (sourceAt : types[source]? = some (some sourceType))
    (carrier : SliceViewType sourceType) :
    ConsumedReferenceOccurrence env root func types upper value := by
  obtain ⟨block, member, defined⟩ := continuation.emitted_definition run live generated
  exact .backing value source op block member defined backing sourceType sourceAt carrier

#print axioms NativeBuilderContinuation.emitted_definition
#print axioms NativeBuilderContinuation.consumedBacking

end Goose.Lower.Validation.ReplacementContentFlowSource
