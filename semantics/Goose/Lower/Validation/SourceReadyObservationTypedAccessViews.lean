import Goose.Lower.Validation.SourceReadyObservationAccess
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyAccess
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before : LS}
  {typingEnv : TEnv} {results : List Ty} {element : Ty} {writable : Bool} {start finish : Nat}

theorem viewOf {place : Place}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyView typingEnv (.of place) start = .ok ((element, writable), finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerView (.of place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerView (.of place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerView (.of place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
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
    (ValueReadyAt state (lowerView (.of place)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerView (.of place)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change SummaryPreservation.NativeRows types (lowerView (.of place) env before).2 at native
  change (lowerView (.of place) env before).2.Ext completed at extension
  change (lowerView (.of place) env before).2.vals.size ≤ completed.vals.size at allocated
  let address := lowerPlace place env before
  let kind := match place with | .var _ | .global _ => SnapshotMode.owner | _ => .borrowed
  let emitted := Lower.emitDef (.snapshot kind address.1) env address.2
  have actual : lowerView (.of place) env before = emitted := by
    cases place <;> rfl
  rw [actual] at native extension allocated
  have tailAdvance : address.2.Adv emitted.2 := adv_emitDef (show Lower.emitDef (.snapshot kind address.1) env address.2 = emitted from rfl)
  have childNative : SummaryPreservation.NativeRows types address.2 := by
    apply native.of_prefix
    exact types_emitDef _ env address.2 _ _ rfl
  have sourceCopy := source
  simp only [Core.tyView] at sourceCopy
  obtain ⟨info, childFinish, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp sourceCopy
  have ready := child info start childFinish childSource generated childNative
    (tailAdvance.ext.trans extension)
    (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.viewOf (show lowerPlace place env before = address from rfl) actual extension allocated
      (generated.lowerPlace place rfl).live (ready.1)
  · exact ReadyCallObservations.viewOf place ready.2

theorem viewValue {expression : Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyView typingEnv (.val expression) start = .ok ((element, writable), finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerView (.val expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerView (.val expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerView (.val expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ childType childStart childFinish,
      Core.tyExpr typingEnv expression childStart = .ok (childType, childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)) :
    (ValueReadyAt state (lowerView (.val expression)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerView (.val expression)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change SummaryPreservation.NativeRows types (lowerView (.val expression) env before).2 at native
  change (lowerView (.val expression) env before).2.Ext completed at extension
  change (lowerView (.val expression) env before).2.vals.size ≤ completed.vals.size at allocated
  let evaluated := lowerExpr expression env before
  let emitted := Lower.emitDef (.sliceView evaluated.1) env evaluated.2
  have actual : lowerView (.val expression) env before = emitted := rfl
  rw [actual] at native extension allocated
  have tailAdvance : evaluated.2.Adv emitted.2 := adv_emitDef (show Lower.emitDef (.sliceView evaluated.1) env evaluated.2 = emitted from rfl)
  have childNative : SummaryPreservation.NativeRows types evaluated.2 := by
    apply native.of_prefix
    exact types_emitDef _ env evaluated.2 _ _ rfl
  have sourceCopy := source
  simp only [Core.tyView] at sourceCopy
  obtain ⟨childType, childFinish, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp sourceCopy
  have ready := child childType start childFinish childSource generated childNative
    (tailAdvance.ext.trans extension)
    (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.viewValue (show lowerExpr expression env before = evaluated from rfl) actual extension allocated
      (generated.lowerExpr expression rfl).live (ready.1)
  · exact ReadyCallObservations.viewValue expression ready.2

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations
