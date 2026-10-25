import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem native_block_stages {vt : Array (Option VTy)} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool} {scope : ScopeId}
    {statements : List Stmt} {value : Option Expr} {le : LEnv} {initial : LS}
    (generated : GeneratedBuilderState initial)
    (loopBounds : LoopBuilderTargets loop initial)
    (native : NativeRows vt (lowerBlock loop bindings want (.mk scope statements value) le initial).2) :
    let initialized := (initSlots bindings le (Goose.Lower.pushScope scope le
      (Goose.Lower.emitEffect (.enter scope) le initial).2).2).2
    let body := lowerStmts loop statements le initialized
    let produced := lowerBlockValue want value le body.2
    GeneratedBuilderState initialized ∧ GeneratedBuilderState body.2 ∧
      NativeRows vt body.2 ∧ NativeRows vt produced.2 := by
  dsimp only
  let entered := (Goose.Lower.emitEffect (.enter scope) le initial).2
  let scopedState := (Goose.Lower.pushScope scope le entered).2
  let initialized := (initSlots bindings le scopedState).2
  let body := lowerStmts loop statements le initialized
  let produced := lowerBlockValue want value le body.2
  have enteredGenerated := generated.emitEffect (.enter scope)
    (rfl : Goose.Lower.emitEffect (.enter scope) le initial = ((), entered))
  have scopedGenerated : GeneratedBuilderState scopedState := by
    rw [show scopedState = (Goose.Lower.pushScope scope le entered).2 from rfl, pushScope_run]
    exact ⟨enteredGenerated.dense, enteredGenerated.live, enteredGenerated.targets⟩
  have initializedGenerated := scopedGenerated.initSlots bindings
    (rfl : initSlots bindings le scopedState = ((), initialized))
  have scopedBlocks : scopedState.blocks = entered.blocks := by
    change (Goose.Lower.pushScope scope le entered).2.blocks = entered.blocks
    rw [pushScope_run]
  have growth : initial.blocks.size ≤ initialized.blocks.size :=
    Nat.le_trans (advB_emitEffect (.enter scope) le initial () entered rfl).ext.1 (by
      rw [← scopedBlocks]
      exact (advB_initSlots bindings le scopedState () initialized rfl).ext.1)
  have bodyGenerated := initializedGenerated.lowerStmts loop statements (loopBounds.mono growth)
    (rfl : lowerStmts loop statements le initialized = body)
  have whole : lowerBlock loop bindings want (.mk scope statements value) le initial =
      (produced.1, (Goose.Lower.popScope le (Goose.Lower.emitEffect (.leave scope) le produced.2).2).2) := by
    simp only [lowerBlock, inScope, bind_run, pure_run]
    rfl
  have producedNative : NativeRows vt produced.2 := by
    apply native.of_prefix
    rw [whole]
    exact (types_emitEffect (.leave scope) le produced.2 _ _ rfl).trans (types_popScope le _ _ _ rfl)
  have bodyNative : NativeRows vt body.2 :=
    producedNative.of_prefix (types_lowerBlockValue want value le body.2 produced.1 produced.2 rfl)
  exact ⟨initializedGenerated, bodyGenerated, bodyNative, producedNative⟩

#print axioms native_block_stages

end Goose.Lower.Validation.SummaryPreservation
