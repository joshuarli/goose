import Goose.Lower.Validation.SourceReadyObservationAccess
import Goose.Lower.Validation.ReplacementContentFlowSourceReadySlices
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.ExpressionTypingSliceOps

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before : LS}
  {typingEnv : TEnv} {results : List Ty} {start finish : Nat}

theorem boundary {bound : Bound}
    (source : Core.tyBound typingEnv bound start = .ok ((), finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerBound bound (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerBound bound (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerBound bound (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ expression, bound = .expr expression ∨ bound = .fromEnd expression →
      ∀ childType childStart childFinish,
      Core.tyExpr typingEnv expression childStart = .ok (childType, childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)) :
    (BoundaryReadyAt state bound (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerBound bound) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  cases bound with
  | omitted => exact ⟨⟨.refl _ _, by simp [lowerBound, pure_run, Bnd.uses]⟩, ReadyCallObservations.boundOmitted⟩
  | expr expression =>
    obtain ⟨integer, childFinish, childSource⟩ := tyBound_child source
    have ready := child expression (.inl rfl) (.int integer) start childFinish childSource
      generated native extension allocated visible
    constructor
    · apply lowerBound_ready
      intro other shape
      rcases shape with same | impossible
      · cases same; exact ready.1
      · cases impossible
    · exact ReadyCallObservations.boundExpr expression ready.2
  | fromEnd expression =>
    obtain ⟨integer, childFinish, childSource⟩ := tyBound_child source
    have ready := child expression (.inr rfl) (.int integer) start childFinish childSource
      generated native extension allocated visible
    constructor
    · apply lowerBound_ready
      intro other shape
      rcases shape with impossible | same
      · cases impossible
      · cases same; exact ready.1
    · exact ReadyCallObservations.boundFromEnd expression ready.2

theorem slice {mutability : Mutability} {view : View}
    {low high : Bound} {origin : OriginId} {type : Ty}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.slice mutability view low high origin) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.slice mutability view low high origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.slice mutability view low high origin)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.slice mutability view low high origin)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (viewChild : ∀ element writable childStart childFinish,
      Core.tyView typingEnv view childStart = .ok ((element, writable), childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) before).2))
    (lowChild : ∀ childStart childFinish,
      Core.tyBound typingEnv low childStart = .ok ((), childFinish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let first := lowerView view env before
      GeneratedBuilderState first.2 → SummaryPreservation.NativeRows types (lowerBound low env first.2).2 →
      (lowerBound low env first.2).2.Ext completed →
      (lowerBound low env first.2).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → (BoundaryReadyAt state low env first.2 ∧
      EmitsOnly (ReadyCallObservations module func state) first.2 ((lowerBound low) env first.2).2))
    (highChild : ∀ childStart childFinish,
      Core.tyBound typingEnv high childStart = .ok ((), childFinish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let first := lowerView view env before
      let second := lowerBound low env first.2
      GeneratedBuilderState second.2 → SummaryPreservation.NativeRows types (lowerBound high env second.2).2 →
      (lowerBound high env second.2).2.Ext completed →
      (lowerBound high env second.2).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → (BoundaryReadyAt state high env second.2 ∧
      EmitsOnly (ReadyCallObservations module func state) second.2 ((lowerBound high) env second.2).2)) :
    (ValueReadyAt state (lowerExpr (.slice mutability view low high origin))
      (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.slice mutability view low high origin)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let first := lowerView view env before
  let second := lowerBound low env first.2
  let third := lowerBound high env second.2
  let emitted := Lower.emitDef (.viewSlice mutability first.1 second.1 third.1 (some origin)) env third.2
  have actual : lowerExpr (.slice mutability view low high origin) env before = emitted := rfl
  change SummaryPreservation.NativeRows types (lowerExpr (.slice mutability view low high origin) env before).2 at native
  change (lowerExpr (.slice mutability view low high origin) env before).2.Ext completed at extension
  change (lowerExpr (.slice mutability view low high origin) env before).2.vals.size ≤ completed.vals.size at allocated
  rw [actual] at native extension allocated
  have tailAdvance : third.2.Adv emitted.2 := adv_emitDef
    (show Lower.emitDef (.viewSlice mutability first.1 second.1 third.1 (some origin)) env third.2 = emitted from rfl)
  have thirdNative := native.of_prefix (types_emitDef _ env third.2 _ _ rfl)
  have thirdExtension := tailAdvance.ext.trans extension
  have thirdAllocated := Nat.le_trans tailAdvance.vals allocated
  have highAdvance := advB_lowerBound high env second.2 third.1 third.2 rfl
  have lowAdvance := advB_lowerBound low env first.2 second.1 second.2 rfl
  have secondNative := thirdNative.of_prefix (types_lowerBound high env second.2 _ _ rfl)
  have secondExtension := highAdvance.ext.trans thirdExtension
  have secondAllocated := Nat.le_trans highAdvance.vals thirdAllocated
  obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish,
    viewSource, lowSource, highSource, rest⟩ := tyExpr_slice_children source
  have readyView := viewChild element writable viewStart viewFinish viewSource generated
    (secondNative.of_prefix (types_lowerBound low env first.2 _ _ rfl))
    (lowAdvance.ext.trans secondExtension) (Nat.le_trans lowAdvance.vals secondAllocated) visible
  have firstGenerated := generated.lowerView view (show lowerView view env before = first from rfl)
  have readyLow := lowChild viewFinish lowFinish lowSource firstGenerated
    secondNative secondExtension secondAllocated visible
  have secondGenerated := firstGenerated.lowerBound low (show lowerBound low env first.2 = second from rfl)
  have readyHigh := highChild lowFinish highFinish highSource secondGenerated thirdNative
    thirdExtension thirdAllocated visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.slice (show lowerView view env before = first from rfl)
      (show lowerBound low env first.2 = second from rfl) (show lowerBound high env second.2 = third from rfl)
      actual extension allocated (secondGenerated.lowerBound high rfl).live (readyView.1) (readyLow.1) (readyHigh.1)
  · exact ReadyCallObservations.slice mutability view low high origin readyView.2 readyLow.2 readyHigh.2

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations
