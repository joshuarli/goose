import Goose.Lower.Validation.SourceReadyObservationAccess
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyArithmetic
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before : LS}
  {typingEnv : TEnv} {results : List Ty} {type : Ty} {start finish : Nat}

theorem unary
    {operation : UnOp} {expression : Expr} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.un operation expression origin) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.un operation expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.un operation expression origin)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.un operation expression origin)
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
    (ValueReadyAt state (lowerExpr (.un operation expression origin))
      (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.un operation expression origin)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change SummaryPreservation.NativeRows types (lowerExpr (.un operation expression origin) env before).2 at native
  change (lowerExpr (.un operation expression origin) env before).2.Ext completed at extension
  change (lowerExpr (.un operation expression origin) env before).2.vals.size ≤ completed.vals.size at allocated
  let evaluated := lowerExpr expression env before
  let integer := (intTyOf evaluated.1 env evaluated.2).1
  let emitted := Lower.emitDef (.un operation integer evaluated.1 (some origin)) env evaluated.2
  have actual : lowerExpr (.un operation expression origin) env before = emitted := by
    simp only [lowerExpr, bind_run, intTyOf_state]
    rfl
  rw [actual] at native extension allocated
  have tailAdvance : evaluated.2.Adv emitted.2 := adv_emitDef (show Lower.emitDef (.un operation integer evaluated.1 (some origin))
    env evaluated.2 = emitted from rfl)
  have childNative : SummaryPreservation.NativeRows types evaluated.2 := by
    apply native.of_prefix
    exact types_emitDef _ env evaluated.2 _ _ rfl
  obtain ⟨childStart, childFinish, integerType, childSource, rest⟩ := tyExpr_un_child source
  have ready := child (.int integerType) childStart childFinish childSource generated childNative
    (tailAdvance.ext.trans extension)
    (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.unary (show lowerExpr expression env before = evaluated from rfl) actual
      extension allocated (generated.lowerExpr expression rfl).live (ready.1)
  · exact ReadyCallObservations.unary operation expression origin ready.2

theorem binary
    {operation : BinOp} {left right : Expr} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.bin operation left right origin) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.bin operation left right origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.bin operation left right origin)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.bin operation left right origin)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (leftChild : ∀ childType childStart childFinish,
      Core.tyExpr typingEnv left childStart = .ok (childType, childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerExpr left (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr left (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr left (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerExpr left) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr left) (lowerEnv typingEnv.mod typingEnv.vars results) before).2))
    (rightChild : ∀ childType childStart childFinish,
      Core.tyExpr typingEnv right childStart = .ok (childType, childFinish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let first := lowerExpr left env before
      GeneratedBuilderState first.2 →
      SummaryPreservation.NativeRows types (lowerExpr right env first.2).2 →
      (lowerExpr right env first.2).2.Ext completed →
      (lowerExpr right env first.2).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → (ValueReadyAt state (lowerExpr right) env first.2 ∧
      EmitsOnly (ReadyCallObservations module func state) first.2 ((lowerExpr right) env first.2).2)) :
    (ValueReadyAt state (lowerExpr (.bin operation left right origin))
      (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.bin operation left right origin)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change SummaryPreservation.NativeRows types (lowerExpr (.bin operation left right origin) env before).2 at native
  change (lowerExpr (.bin operation left right origin) env before).2.Ext completed at extension
  change (lowerExpr (.bin operation left right origin) env before).2.vals.size ≤ completed.vals.size at allocated
  let first := lowerExpr left env before
  let second := lowerExpr right env first.2
  let integer := (intTyOf first.1 env second.2).1
  let emitted := Lower.emitDef (.bin operation integer first.1 second.1 (some origin)) env second.2
  have actual : lowerExpr (.bin operation left right origin) env before = emitted := by
    simp only [lowerExpr, bind_run, intTyOf_state]
    rfl
  rw [actual] at native extension allocated
  have tailAdvance : second.2.Adv emitted.2 := adv_emitDef (show Lower.emitDef (.bin operation integer first.1 second.1 (some origin))
    env second.2 = emitted from rfl)
  have secondNative : SummaryPreservation.NativeRows types second.2 := by
    apply native.of_prefix
    exact types_emitDef _ env second.2 _ _ rfl
  have secondExtension := tailAdvance.ext.trans extension
  have secondAllocated := Nat.le_trans tailAdvance.vals allocated
  have rightAdvance := advB_lowerExpr right env first.2 second.1 second.2 rfl
  obtain ⟨leftStart, leftFinish, rightStart, rightFinish, integerType, leftSource, rightSource, rest⟩ :=
    tyExpr_bin_children source
  have readyLeft := leftChild (.int integerType) leftStart leftFinish leftSource generated
    (secondNative.of_prefix (types_lowerExpr right env first.2 _ _ rfl))
    (rightAdvance.ext.trans secondExtension) (Nat.le_trans rightAdvance.vals secondAllocated) visible
  have firstGenerated := generated.lowerExpr left (show lowerExpr left env before = first from rfl)
  have readyRight := rightChild (.int integerType) rightStart rightFinish rightSource firstGenerated
    secondNative secondExtension secondAllocated visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.binary (show lowerExpr left env before = first from rfl)
      (show lowerExpr right env first.2 = second from rfl) actual extension allocated
      (firstGenerated.lowerExpr right rfl).live (readyLeft.1) (readyRight.1)
  · exact ReadyCallObservations.binary operation left right origin readyLeft.2 readyRight.2

theorem conversion
    {kind : ConvKind} {target : Ty} {expression : Expr} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.conv kind target expression origin) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.conv kind target expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.conv kind target expression origin)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.conv kind target expression origin)
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
    (ValueReadyAt state (lowerExpr (.conv kind target expression origin))
      (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.conv kind target expression origin)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change SummaryPreservation.NativeRows types (lowerExpr (.conv kind target expression origin) env before).2 at native
  change (lowerExpr (.conv kind target expression origin) env before).2.Ext completed at extension
  change (lowerExpr (.conv kind target expression origin) env before).2.vals.size ≤ completed.vals.size at allocated
  let evaluated := lowerExpr expression env before
  let integer := (intTyOf evaluated.1 env evaluated.2).1
  let destination := match target with | .int integerType => integerType | _ => integer
  let emitted := Lower.emitDef (.conv kind integer destination evaluated.1 (some origin)) env evaluated.2
  have actual : lowerExpr (.conv kind target expression origin) env before = emitted := by
    cases target <;> simp only [lowerExpr, bind_run, intTyOf_state] <;> rfl
  rw [actual] at native extension allocated
  have tailAdvance : evaluated.2.Adv emitted.2 := adv_emitDef (show Lower.emitDef (.conv kind integer destination evaluated.1 (some origin))
    env evaluated.2 = emitted from rfl)
  have childNative : SummaryPreservation.NativeRows types evaluated.2 := by
    apply native.of_prefix
    exact types_emitDef _ env evaluated.2 _ _ rfl
  obtain ⟨integerType, destinationType, childStart, childFinish, childSource, rest⟩ :=
    tyExpr_conversion_child source
  have ready := child (.int integerType) childStart childFinish childSource generated childNative
    (tailAdvance.ext.trans extension)
    (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.conversion (show lowerExpr expression env before = evaluated from rfl) actual
      extension allocated (generated.lowerExpr expression rfl).live (ready.1)
  · exact ReadyCallObservations.conversion kind target expression origin ready.2

theorem comparison
    {operation : CmpOp} {left right : Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.cmp operation left right) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.cmp operation left right) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.cmp operation left right)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.cmp operation left right)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (leftChild : ∀ childType childStart childFinish,
      Core.tyExpr typingEnv left childStart = .ok (childType, childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types
        (lowerExpr left (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr left (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr left (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerExpr left) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr left) (lowerEnv typingEnv.mod typingEnv.vars results) before).2))
    (rightChild : ∀ childType childStart childFinish,
      Core.tyExpr typingEnv right childStart = .ok (childType, childFinish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let first := lowerExpr left env before
      GeneratedBuilderState first.2 →
      SummaryPreservation.NativeRows types (lowerExpr right env first.2).2 →
      (lowerExpr right env first.2).2.Ext completed →
      (lowerExpr right env first.2).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → (ValueReadyAt state (lowerExpr right) env first.2 ∧
      EmitsOnly (ReadyCallObservations module func state) first.2 ((lowerExpr right) env first.2).2)) :
    (ValueReadyAt state (lowerExpr (.cmp operation left right))
      (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.cmp operation left right)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change SummaryPreservation.NativeRows types (lowerExpr (.cmp operation left right) env before).2 at native
  change (lowerExpr (.cmp operation left right) env before).2.Ext completed at extension
  change (lowerExpr (.cmp operation left right) env before).2.vals.size ≤ completed.vals.size at allocated
  let first := lowerExpr left env before
  let second := lowerExpr right env first.2
  let operandType := (valTy first.1 env second.2).1
  let instruction := match operandType with
    | .data (.int integer) => Op.cmp operation integer first.1 second.1
    | _ => Op.boolCmp operation first.1 second.1
  let emitted := Lower.emitDef instruction env second.2
  have classification : valTy first.1 env second.2 = (operandType, second.2) :=
    Prod.ext rfl (valTy_eq rfl)
  have actual : lowerExpr (.cmp operation left right) env before = emitted := by
    simp only [lowerExpr, bind_run]
    change (match (valTy first.1 env second.2).1 with
      | .data (.int integer) => Lower.emitDef (.cmp operation integer first.1 second.1)
      | _ => Lower.emitDef (.boolCmp operation first.1 second.1))
        env (valTy first.1 env second.2).2 = emitted
    rw [classification]
    dsimp only [emitted, instruction]
    cases operandType with
    | data dataType => cases dataType <;> rfl
    | view mutability element => rfl
  rw [actual] at native extension allocated
  have tailAdvance : second.2.Adv emitted.2 := adv_emitDef (show Lower.emitDef (instruction)
    env second.2 = emitted from rfl)
  have secondNative : SummaryPreservation.NativeRows types second.2 := by
    apply native.of_prefix
    exact types_emitDef _ env second.2 _ _ rfl
  have secondExtension := tailAdvance.ext.trans extension
  have secondAllocated := Nat.le_trans tailAdvance.vals allocated
  have rightAdvance := advB_lowerExpr right env first.2 second.1 second.2 rfl
  obtain ⟨leftType, rightType, leftFinish, rightFinish, leftSource, rightSource, rest⟩ :=
    tyExpr_comparison_children source
  have readyLeft := leftChild leftType start leftFinish leftSource generated
    (secondNative.of_prefix (types_lowerExpr right env first.2 _ _ rfl))
    (rightAdvance.ext.trans secondExtension) (Nat.le_trans rightAdvance.vals secondAllocated) visible
  have firstGenerated := generated.lowerExpr left (show lowerExpr left env before = first from rfl)
  have readyRight := rightChild rightType leftFinish rightFinish rightSource firstGenerated
    secondNative secondExtension secondAllocated visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.comparison (show lowerExpr left env before = first from rfl)
      (show lowerExpr right env first.2 = second from rfl) actual extension allocated
      (firstGenerated.lowerExpr right rfl).live (readyLeft.1) (readyRight.1)
  · exact ReadyCallObservations.comparison operation left right readyLeft.2 readyRight.2

theorem logicalNot
    {expression : Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.not expression) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.not expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.not expression)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.not expression)
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
    (ValueReadyAt state (lowerExpr (.not expression))
      (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before ((lowerExpr (.not expression)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change SummaryPreservation.NativeRows types (lowerExpr (.not expression) env before).2 at native
  change (lowerExpr (.not expression) env before).2.Ext completed at extension
  change (lowerExpr (.not expression) env before).2.vals.size ≤ completed.vals.size at allocated
  let evaluated := lowerExpr expression env before
  let emitted := Lower.emitDef (.boolNot evaluated.1) env evaluated.2
  have actual : lowerExpr (.not expression) env before = emitted := by
    rfl
  rw [actual] at native extension allocated
  have tailAdvance : evaluated.2.Adv emitted.2 := adv_emitDef (show Lower.emitDef (.boolNot evaluated.1)
    env evaluated.2 = emitted from rfl)
  have childNative : SummaryPreservation.NativeRows types evaluated.2 := by
    apply native.of_prefix
    exact types_emitDef _ env evaluated.2 _ _ rfl
  obtain ⟨childFinish, childSource, resultEq⟩ := tyExpr_not_child source
  have ready := child .bool start childFinish childSource generated childNative
    (tailAdvance.ext.trans extension)
    (Nat.le_trans tailAdvance.vals allocated) visible
  constructor
  · unfold ValueReadyAt
    rw [actual]
    exact frame.not actual
      extension allocated (generated.lowerExpr expression rfl).live (ready.1)
  · exact ReadyCallObservations.logicalNot expression ready.2

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyValueObservations
