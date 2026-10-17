import Goose.Lower.Validation.SourceReadyObservationAccess
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyConstructors
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before : LS}
  {typingEnv : TEnv} {results : List Ty} {type : Ty} {start finish : Nat}

theorem array {arrayType : Ty} {expressions : List Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.arrLit arrayType expressions) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.arrLit arrayType expressions) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.arrLit arrayType expressions) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.arrLit arrayType expressions) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (children : ∀ element childStart childFinish,
      Core.tyExprsAs typingEnv element expressions childStart = .ok ((), childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValuesReadyAt state (lowerExprs expressions) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExprs expressions) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)) :
    (ValueReadyAt state (lowerExpr (.arrLit arrayType expressions)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.arrLit arrayType expressions)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let values := lowerExprs expressions env before
  let emitted := Lower.emitDef (.arrLit arrayType values.1) env values.2
  have actual : lowerExpr (.arrLit arrayType expressions) env before = emitted := rfl
  change SummaryPreservation.NativeRows types (lowerExpr (.arrLit arrayType expressions) env before).2 at native
  change (lowerExpr (.arrLit arrayType expressions) env before).2.Ext completed at extension
  change (lowerExpr (.arrLit arrayType expressions) env before).2.vals.size ≤ completed.vals.size at allocated
  rw [actual] at native extension allocated
  have tailAdvance : values.2.Adv emitted.2 := adv_emitDef
    (show Lower.emitDef (.arrLit arrayType values.1) env values.2 = emitted from rfl)
  obtain ⟨resultEq, element, childStart, childFinish, arrayShape, count, childrenSource⟩ :=
    tyExpr_arrayLiteral_children source
  have ready := children element childStart childFinish childrenSource generated
    (native.of_prefix (types_emitDef _ env values.2 _ _ rfl))
    (tailAdvance.ext.trans extension) (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.array (show lowerExprs expressions env before = values from rfl) actual extension allocated
      (generated.lowerExprs expressions rfl).live (ready.1)
  · exact ReadyCallObservations.arrayLiteral arrayType expressions ready.2

theorem «structure» {structureType : Ty} {expressions : List Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.structLit structureType expressions) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.structLit structureType expressions) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.structLit structureType expressions) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.structLit structureType expressions) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (children : ∀ fieldTypes childStart childFinish,
      Core.tyStructExprs typingEnv fieldTypes expressions childStart = .ok ((), childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValuesReadyAt state (lowerExprs expressions) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExprs expressions) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)) :
    (ValueReadyAt state (lowerExpr (.structLit structureType expressions)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.structLit structureType expressions)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let values := lowerExprs expressions env before
  let emitted := Lower.emitDef (.structLit structureType values.1) env values.2
  have actual : lowerExpr (.structLit structureType expressions) env before = emitted := rfl
  change SummaryPreservation.NativeRows types (lowerExpr (.structLit structureType expressions) env before).2 at native
  change (lowerExpr (.structLit structureType expressions) env before).2.Ext completed at extension
  change (lowerExpr (.structLit structureType expressions) env before).2.vals.size ≤ completed.vals.size at allocated
  rw [actual] at native extension allocated
  have tailAdvance : values.2.Adv emitted.2 := adv_emitDef
    (show Lower.emitDef (.structLit structureType values.1) env values.2 = emitted from rfl)
  obtain ⟨resultEq, descriptor, definitionFinish, childStart, childFinish, definition, childrenSource⟩ :=
    tyExpr_structLiteral_children source
  have ready := children (descriptor.fields.toList.map (·.ty)) childStart childFinish childrenSource generated
    (native.of_prefix (types_emitDef _ env values.2 _ _ rfl))
    (tailAdvance.ext.trans extension) (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.structure (show lowerExprs expressions env before = values from rfl) actual extension allocated
      (generated.lowerExprs expressions rfl).live (ready.1)
  · exact ReadyCallObservations.structLiteral structureType expressions ready.2

theorem fill
    {arrayType : Ty} {expression : Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.fill arrayType expression) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.fill arrayType expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.fill arrayType expression)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.fill arrayType expression)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
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
    (ValueReadyAt state (lowerExpr (.fill arrayType expression))
      (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.fill arrayType expression)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change SummaryPreservation.NativeRows types (lowerExpr (.fill arrayType expression) env before).2 at native
  change (lowerExpr (.fill arrayType expression) env before).2.Ext completed at extension
  change (lowerExpr (.fill arrayType expression) env before).2.vals.size ≤ completed.vals.size at allocated
  let evaluated := lowerExpr expression env before
  let emitted := Lower.emitDef (.arrFill arrayType evaluated.1) env evaluated.2
  have actual : lowerExpr (.fill arrayType expression) env before = emitted := by
    rfl
  rw [actual] at native extension allocated
  have tailAdvance : evaluated.2.Adv emitted.2 := adv_emitDef (show Lower.emitDef (.arrFill arrayType evaluated.1)
    env evaluated.2 = emitted from rfl)
  have childNative : SummaryPreservation.NativeRows types evaluated.2 := by
    apply native.of_prefix
    exact types_emitDef _ env evaluated.2 _ _ rfl
  obtain ⟨resultEq, element, size, childStart, childFinish, arrayShape, childSource⟩ :=
    tyExpr_fill_child source
  have ready := child element childStart childFinish childSource generated childNative
    (tailAdvance.ext.trans extension)
    (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.fill (show lowerExpr expression env before = evaluated from rfl) actual
      extension allocated (generated.lowerExpr expression rfl).live (ready.1)
  · exact ReadyCallObservations.arrayFill arrayType expression ready.2

theorem length {view : View}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.len view) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.len view) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.len view) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.len view) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ element writable childStart childFinish,
      Core.tyView typingEnv view childStart = .ok ((element, writable), childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)) :
    (ValueReadyAt state (lowerExpr (.len view)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.len view)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let viewed := lowerView view env before
  let emitted := Lower.emitDef (.viewLen viewed.1) env viewed.2
  have actual : lowerExpr (.len view) env before = emitted := rfl
  change SummaryPreservation.NativeRows types (lowerExpr (.len view) env before).2 at native
  change (lowerExpr (.len view) env before).2.Ext completed at extension
  change (lowerExpr (.len view) env before).2.vals.size ≤ completed.vals.size at allocated
  rw [actual] at native extension allocated
  have tailAdvance : viewed.2.Adv emitted.2 := adv_emitDef
    (show Lower.emitDef (.viewLen viewed.1) env viewed.2 = emitted from rfl)
  have sourceCopy := source
  simp only [Core.tyExpr] at sourceCopy
  obtain ⟨pair, childFinish, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp sourceCopy
  have ready := child pair.1 pair.2 start childFinish childSource generated
    (native.of_prefix (types_emitDef _ env viewed.2 _ _ rfl))
    (tailAdvance.ext.trans extension) (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.length (show lowerView view env before = viewed from rfl) actual extension allocated
      (generated.lowerView view rfl).live (ready.1)
  · exact ReadyCallObservations.length view ready.2

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations
