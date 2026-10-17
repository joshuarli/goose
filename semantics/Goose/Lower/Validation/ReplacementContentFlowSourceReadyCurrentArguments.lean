import Goose.Lower.Validation.ReplacementContentFlowSourceReadyArgumentRoots
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCallContents

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before after : LS}
  {provenance : Prov} {results : Array (List RootRef)} {env : LEnv}
  {output : ValueId} {mutability nativeMutability : Mutability}
  {sourceEnv : PEnv} {sourcePlace : Place} {physicalRoots : List RootRef}

theorem SourceReadyFrame.current_variable_argument_content
    (frame : SourceReadyFrame module callees func types state completed)
    (canonical : state.CanonicalWithin func types provenance)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep results types (provenance, false) instruction = (provenance, false))
    (growth : (start func types).Extends state)
    {variableId : VarId} {typingEnv : TEnv} {info : PlaceInfo} {startOffset finishOffset : Nat}
    (run : lowerArg (.byRef mutability (.var variableId)) env before = (output, after))
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (extension : after.Ext completed)
    (physical : ReadAddressPhysical sourceEnv sourcePlace physicalRoots)
    (source : Core.tyPlace typingEnv (.var variableId) startOffset = .ok (info, finishOffset))
    (reference : info.ty.isRefLike = true)
    (slots : VisibleSlotsReady typingEnv state)
    (valueBound : output < state.values.size)
    (native : types[output]? = some (some (.data (.ref nativeMutability info.ty))))
    (below : rootsAt provenance.vals output ⊆ physicalRoots)
    (available : flowAt state.values output ≠ .pending) :
    content func state (flowAt state.values output) ≠ .pending := by
  have member := frame.native_variable_argument_root valuesSize definitions quiet run bounded live extension
  exact physical.local_content_ready canonical growth source reference slots valueBound native below member available

theorem SourceReadyFrame.current_forwarded_argument_content
    (frame : SourceReadyFrame module callees func types state completed)
    (canonical : state.CanonicalWithin func types provenance)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep results types (provenance, false) instruction = (provenance, false))
    (growth : (start func types).Extends state)
    {variableId : VarId} {address holder : ValueId} {first middle : LS} {payload : Ty}
    (slotRun : Lower.emitDef (.slotAddr variableId) env before = (address, first))
    (loadRun : Lower.emitDef (.load address) env first = (holder, middle))
    (borrowRun : Lower.borrowTo mutability holder env middle = (output, after))
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (extension : after.Ext completed)
    (seed : RootRef.param variableId ∈ rootsAt provenance.slots variableId)
    (holderReference : valRefLike types holder = true)
    (physical : ReadAddressPhysical sourceEnv sourcePlace physicalRoots)
    (reference : payload.isRefLike = true)
    (valueBound : output < state.values.size)
    (native : types[output]? = some (some (.data (.ref nativeMutability payload))))
    (below : rootsAt provenance.vals output ⊆ physicalRoots)
    (available : flowAt state.values output ≠ .pending) :
    content func state (flowAt state.values output) ≠ .pending := by
  have member := frame.native_forwarded_argument_root valuesSize definitions quiet slotRun loadRun borrowRun
    bounded live extension seed holderReference
  exact physical.parameter_content_ready canonical growth reference valueBound native below member available

#print axioms SourceReadyFrame.current_variable_argument_content
#print axioms SourceReadyFrame.current_forwarded_argument_content

end Goose.Lower.Validation.ReplacementContentFlowSource
