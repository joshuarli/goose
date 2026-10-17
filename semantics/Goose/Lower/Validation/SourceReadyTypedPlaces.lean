import Goose.Lower.Validation.ReplacementContentFlowSourceReadyAccess
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before : LS}
  {typingEnv : TEnv} {results : List Ty} {info : PlaceInfo} {start finish : Nat}

theorem SourceReadyFrame.typedField {owner : Place} {index : Nat}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyPlace typingEnv (.field owner index) start = .ok (info, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerPlace (.field owner index) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerPlace (.field owner index) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerPlace (.field owner index) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ ownerInfo childStart childFinish,
      Core.tyPlace typingEnv owner childStart = .ok (ownerInfo, childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerPlace owner (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerPlace owner (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerPlace owner (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerPlace owner) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    ValueReadyAt state (lowerPlace (.field owner index)) (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change ValueReadyAt state (lowerPlace (.field owner index)) env before
  change SummaryPreservation.NativeRows types (lowerPlace (.field owner index) env before).2 at native
  change (lowerPlace (.field owner index) env before).2.Ext completed at extension
  change (lowerPlace (.field owner index) env before).2.vals.size ≤ completed.vals.size at allocated
  let address := lowerPlace owner env before
  let emitted := Lower.emitDef (.fieldAddr address.1 index) env address.2
  have actual : lowerPlace (.field owner index) env before = emitted := rfl
  rw [actual] at native extension allocated
  unfold ValueReadyAt
  rw [actual]
  have tailAdvance : address.2.Adv emitted.2 := adv_emitDef (show Lower.emitDef (.fieldAddr address.1 index) env address.2 = emitted from rfl)
  have childNative : SummaryPreservation.NativeRows types address.2 := by
    apply native.of_prefix
    exact types_emitDef _ env address.2 _ _ rfl
  have sourceCopy := source
  simp only [Core.tyPlace] at sourceCopy
  obtain ⟨ownerInfo, childFinish, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp sourceCopy
  have ready := child ownerInfo start childFinish childSource generated childNative
    (tailAdvance.ext.trans extension)
    (Nat.le_trans tailAdvance.vals allocated) visible
  exact frame.field (show lowerPlace owner env before = address from rfl) actual extension allocated
    (generated.lowerPlace owner rfl).live ready

theorem typed_ready_dereference {expression : Expr}
    (ordinary : Core.sliceRefTy typingEnv expression = none)
    (source : Core.tyPlace typingEnv (.deref expression) start = .ok (info, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerPlace (.deref expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerPlace (.deref expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerPlace (.deref expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ childType childStart childFinish,
      Core.tyExpr typingEnv expression childStart = .ok (childType, childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    ValueReadyAt state (lowerPlace (.deref expression)) (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  obtain ⟨mutability, childFinish, childSource⟩ := tyPlace_deref_child ordinary source
  exact child (.ref mutability info.ty) start childFinish childSource generated native extension allocated visible

theorem SourceReadyFrame.typedElement {view : View} {index : Expr} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyPlace typingEnv (.elem view index origin) start = .ok (info, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerPlace (.elem view index origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerPlace (.elem view index origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerPlace (.elem view index origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (viewChild : ∀ element writable childStart childFinish,
      Core.tyView typingEnv view childStart = .ok ((element, writable), childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (indexChild : ∀ childType childStart childFinish,
      Core.tyExpr typingEnv index childStart = .ok (childType, childFinish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let first := lowerView view env before
      GeneratedBuilderState first.2 → SummaryPreservation.NativeRows types (lowerExpr index env first.2).2 →
      (lowerExpr index env first.2).2.Ext completed →
      (lowerExpr index env first.2).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → ValueReadyAt state (lowerExpr index) env first.2) :
    ValueReadyAt state (lowerPlace (.elem view index origin)) (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let first := lowerView view env before
  let second := lowerExpr index env first.2
  let emitted := Lower.emitDef (.indexChecked first.1 second.1 (some origin)) env second.2
  have actual : lowerPlace (.elem view index origin) env before = emitted := rfl
  change SummaryPreservation.NativeRows types (lowerPlace (.elem view index origin) env before).2 at native
  change (lowerPlace (.elem view index origin) env before).2.Ext completed at extension
  change (lowerPlace (.elem view index origin) env before).2.vals.size ≤ completed.vals.size at allocated
  change ValueReadyAt state (lowerPlace (.elem view index origin)) env before
  rw [actual] at native extension allocated
  unfold ValueReadyAt
  rw [actual]
  have tailAdvance : second.2.Adv emitted.2 := adv_emitDef
    (show Lower.emitDef (.indexChecked first.1 second.1 (some origin)) env second.2 = emitted from rfl)
  have secondNative : SummaryPreservation.NativeRows types second.2 :=
    native.of_prefix (types_emitDef _ env second.2 _ _ rfl)
  have secondExtension := tailAdvance.ext.trans extension
  have secondAllocated := Nat.le_trans tailAdvance.vals allocated
  have indexAdvance := advB_lowerExpr index env first.2 second.1 second.2 rfl
  obtain ⟨viewStart, viewFinish, indexFinish, writable, integer, viewSource, indexSource⟩ := tyPlace_elem_children source
  have readyView := viewChild info.ty writable viewStart viewFinish viewSource generated
    (secondNative.of_prefix (types_lowerExpr index env first.2 _ _ rfl))
    (indexAdvance.ext.trans secondExtension) (Nat.le_trans indexAdvance.vals secondAllocated) visible
  have firstGenerated := generated.lowerView view (show lowerView view env before = first from rfl)
  have readyIndex := indexChild (.int integer) viewFinish indexFinish indexSource firstGenerated
    secondNative secondExtension secondAllocated visible
  exact frame.element (show lowerView view env before = first from rfl)
    (show lowerExpr index env first.2 = second from rfl) actual extension allocated
    (firstGenerated.lowerExpr index rfl).live readyView readyIndex

end Goose.Lower.Validation.ReplacementContentFlowSource
