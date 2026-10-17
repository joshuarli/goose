import Goose.Lower.Validation.SourceReadyObservationAccess
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyMemory
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyConstructors
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem pushOptional {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {initial : LS}
    (owner : Place) (element : Expr) (origin : Option OriginId)
    (ownerChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace owner le initial).2)
    (elementChild : EmitsOnly (ReadyCallObservations module func state) (lowerPlace owner le initial).2
      (lowerExpr element le (lowerPlace owner le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr (.push owner element origin) le initial).2 :=
  (ownerChild.trans elementChild).trans (emitDefinition
    (.push (lowerPlace owner le initial).1 (lowerExpr element le (lowerPlace owner le initial).2).1 origin)
    (by intros; intro same; cases same) le _ _ _ rfl)

end Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before : LS}
  {typingEnv : TEnv} {results : List Ty} {type : Ty} {start finish : Nat}

theorem pop {owner : Place} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.pop owner origin) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.pop owner origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.pop owner origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.pop owner origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ info childStart childFinish,
      Core.tyPlace typingEnv owner childStart = .ok (info, childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerPlace owner (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerPlace owner (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerPlace owner (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerPlace owner) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerPlace owner) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)) :
    (ValueReadyAt state (lowerExpr (.pop owner origin)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.pop owner origin)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace owner env before
  let emitted := Lower.emitDef (.pop address.1 (some origin)) env address.2
  have actual : lowerExpr (.pop owner origin) env before = emitted := rfl
  change SummaryPreservation.NativeRows types (lowerExpr (.pop owner origin) env before).2 at native
  change (lowerExpr (.pop owner origin) env before).2.Ext completed at extension
  change (lowerExpr (.pop owner origin) env before).2.vals.size ≤ completed.vals.size at allocated
  rw [actual] at native extension allocated
  have tailAdvance : address.2.Adv emitted.2 := adv_emitDef
    (show Lower.emitDef (.pop address.1 (some origin)) env address.2 = emitted from rfl)
  obtain ⟨info, childStart, childFinish, childSource, rest⟩ := tyExpr_pop_owner source
  have ready := child info childStart childFinish childSource generated
    (native.of_prefix (types_emitDef _ env address.2 _ _ rfl))
    (tailAdvance.ext.trans extension) (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.pop (show lowerPlace owner env before = address from rfl) actual extension allocated
      (generated.lowerPlace owner rfl).live (ready.1)
  · exact ReadyCallObservations.pop owner origin ready.2

theorem push {owner : Place} {expression : Expr} {origin : Option OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.push owner expression origin) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.push owner expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.push owner expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.push owner expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (ownerChild : ∀ info childStart childFinish,
      Core.tyPlace typingEnv owner childStart = .ok (info, childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerPlace owner (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerPlace owner (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerPlace owner (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerPlace owner) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerPlace owner) (lowerEnv typingEnv.mod typingEnv.vars results) before).2))
    (valueChild : ∀ childType childStart childFinish,
      Core.tyExpr typingEnv expression childStart = .ok (childType, childFinish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let first := lowerPlace owner env before
      GeneratedBuilderState first.2 →
      SummaryPreservation.NativeRows types (lowerExpr expression env first.2).2 →
      (lowerExpr expression env first.2).2.Ext completed →
      (lowerExpr expression env first.2).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → (ValueReadyAt state (lowerExpr expression) env first.2 ∧
      EmitsOnly (ReadyCallObservations module func state) first.2 ((lowerExpr expression) env first.2).2)) :
    (ValueReadyAt state (lowerExpr (.push owner expression origin)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.push owner expression origin)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let first := lowerPlace owner env before
  let second := lowerExpr expression env first.2
  let emitted := Lower.emitDef (.push first.1 second.1 origin) env second.2
  have actual : lowerExpr (.push owner expression origin) env before = emitted := rfl
  change SummaryPreservation.NativeRows types (lowerExpr (.push owner expression origin) env before).2 at native
  change (lowerExpr (.push owner expression origin) env before).2.Ext completed at extension
  change (lowerExpr (.push owner expression origin) env before).2.vals.size ≤ completed.vals.size at allocated
  rw [actual] at native extension allocated
  have tailAdvance : second.2.Adv emitted.2 := adv_emitDef
    (show Lower.emitDef (.push first.1 second.1 origin) env second.2 = emitted from rfl)
  have secondNative := native.of_prefix (types_emitDef _ env second.2 _ _ rfl)
  have secondExtension := tailAdvance.ext.trans extension
  have secondAllocated := Nat.le_trans tailAdvance.vals allocated
  have valueAdvance := advB_lowerExpr expression env first.2 second.1 second.2 rfl
  obtain ⟨info, element, ownerStart, ownerFinish, valueStart, valueFinish,
    ownerSource, ownerElement, valueSource, resultEq⟩ := tyExpr_push_children source
  have readyOwner := ownerChild info ownerStart ownerFinish ownerSource generated
    (secondNative.of_prefix (types_lowerExpr expression env first.2 _ _ rfl))
    (valueAdvance.ext.trans secondExtension) (Nat.le_trans valueAdvance.vals secondAllocated) visible
  have firstGenerated := generated.lowerPlace owner (show lowerPlace owner env before = first from rfl)
  have readyValue := valueChild element valueStart valueFinish valueSource firstGenerated
    secondNative secondExtension secondAllocated visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    obtain ⟨tail, ready⟩ := frame.emitDef
      (show Lower.emitDef (.push first.1 second.1 origin) env second.2 = emitted from rfl)
      extension allocated (firstGenerated.lowerExpr expression rfl).live
      (by
        intro live operand member
        rcases (show operand = first.1 ∨ operand = second.1 from by simpa [Op.uses] using member) with same | same
        · subst operand
          exact (readyOwner.1).2 ((dead_lowerExpr expression).live_before (le := env) rfl live)
        · subst operand
          exact (readyValue.1).2 live)
      (by intro _ address impossible; cases impossible)
      (by intro _ fn arguments callOrigin impossible; cases impossible)
    exact ⟨(readyOwner.1).1.trans ((readyValue.1).1.trans tail), ready⟩
  · exact ReadyCallObservations.pushOptional owner expression origin readyOwner.2 readyValue.2

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations
