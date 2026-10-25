import Goose.Lower.Validation.SourceReadyObservationAccess
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReferences
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem reference
    {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv : TEnv} {results : List Ty} {type : Ty} {start finish : Nat}
    {mutability : Mutability} {place : Place}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.ref mutability place) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.ref mutability place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.ref mutability place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.ref mutability place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ info childStart childFinish,
      Core.tyPlace typingEnv place childStart = .ok (info, childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)) :
    (ValueReadyAt state (lowerExpr (.ref mutability place)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.ref mutability place)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let borrowed := Lower.borrowTo mutability address.1 env address.2
  have actual : lowerExpr (.ref mutability place) env before = borrowed := rfl
  change SummaryPreservation.NativeRows types (lowerExpr (.ref mutability place) env before).2 at native
  change (lowerExpr (.ref mutability place) env before).2.Ext completed at extension
  change (lowerExpr (.ref mutability place) env before).2.vals.size ≤ completed.vals.size at allocated
  rw [actual] at native extension allocated
  have tailAdvance : address.2.Adv borrowed.2 := advB_borrowTo mutability address.1 env address.2 _ _ rfl
  have childNative : SummaryPreservation.NativeRows types address.2 :=
    native.of_prefix (types_borrowTo mutability address.1 env address.2 _ _ rfl)
  obtain ⟨info, childFinish, childSource, rest⟩ := tyExpr_ref_place source
  have ready := child info start childFinish childSource generated childNative
    (tailAdvance.ext.trans extension) (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.reference (show lowerPlace place env before = address from rfl) actual extension allocated
      (generated.lowerPlace place rfl).live (ready.1)
  · exact ReadyCallObservations.reference mutability place ready.2

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations
