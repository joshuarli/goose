import Goose.Lower.Validation.SourceReadyTypedBlocks
import Goose.Lower.Validation.SourceReadyObservationTypedControlConditional

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.observedTypedBlock {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv : TEnv} {results : List Ty} {sourcePre : List (VarId × Ty)}
    {pre : List (SlotId × ValueId × OriginId)} {loop : Option LoopCtx} {want : Bool}
    {scope start finish : Nat} {statements : List Stmt} {value : Option Expr} {type : Ty}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyBlock typingEnv sourcePre (.mk scope statements value) start = .ok (type, finish))
    (generated : GeneratedBuilderState before) (targets : LoopBuilderTargets loop before)
    (native : SummaryPreservation.NativeRows types
      (Lower.lowerBlock loop pre want (.mk scope statements value) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (Lower.lowerBlock loop pre want (.mk scope statements value) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (Lower.lowerBlock loop pre want (.mk scope statements value) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (preCorrespondence : ∀ slot type, (slot, type) ∈ sourcePre → ∃ input origin, (slot, input, origin) ∈ pre)
    (preSlots : ∀ slot input origin, (slot, input, origin) ∈ pre → slot < func.slots.size)
    (preReady : before.cur.isSome = true → ∀ slot input origin, (slot, input, origin) ∈ pre →
      flowAt state.values input ≠ .pending)
    (counter : ∀ context header integer index, loop = some context → context.cont = .next header integer index →
      flowAt state.values index ≠ .pending)
    (statementsChild : ∀ declared output statementStart valueStart,
      declarePre { typingEnv with scopes := scope :: typingEnv.scopes } scope sourcePre start = .ok (declared, statementStart) →
      Core.tyStmts declared scope statements statementStart = .ok (output, valueStart) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let entered := (emitEffect (.enter scope) env before).2
      let pushed := { entered with stack := scope :: entered.stack }
      let initialized := (Lower.initSlots pre env pushed).2
      GeneratedBuilderState initialized → LoopBuilderTargets loop initialized →
      SummaryPreservation.NativeRows types (lowerStmts loop statements env initialized).2 →
      (lowerStmts loop statements env initialized).2.Ext completed →
      (lowerStmts loop statements env initialized).2.vals.size ≤ completed.vals.size →
      (initialized.cur.isSome = true → VisibleSlotsReady declared state) →
      (∀ context header integer index, loop = some context → context.cont = .next header integer index →
        flowAt state.values index ≠ .pending) →
      (EmitsOnly (ReadyOperands state) initialized (lowerStmts loop statements env initialized).2 ∧
        ((lowerStmts loop statements env initialized).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) initialized (lowerStmts loop statements env initialized).2)
    (valueChild : ∀ declared output statementStart valueStart expression,
      declarePre { typingEnv with scopes := scope :: typingEnv.scopes } scope sourcePre start = .ok (declared, statementStart) →
      Core.tyStmts declared scope statements statementStart = .ok (output, valueStart) →
      value = some expression → Core.tyExpr output expression valueStart = .ok (type, finish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let entered := (emitEffect (.enter scope) env before).2
      let pushed := { entered with stack := scope :: entered.stack }
      let initialized := (Lower.initSlots pre env pushed).2
      let executed := (lowerStmts loop statements env initialized).2
      GeneratedBuilderState executed →
      SummaryPreservation.NativeRows types (lowerExpr expression env executed).2 →
      (lowerExpr expression env executed).2.Ext completed →
      (lowerExpr expression env executed).2.vals.size ≤ completed.vals.size →
      (executed.cur.isSome = true → VisibleSlotsReady output state) →
      ValueReadyAt state (lowerExpr expression) env executed ∧
      EmitsOnly (ReadyCallObservations module func state) executed (lowerExpr expression env executed).2) :
    ((EmitsOnly (ReadyOperands state) before
        (Lower.lowerBlock loop pre want (.mk scope statements value) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      (want = true → (Lower.lowerBlock loop pre want (.mk scope statements value) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        flowAt state.values (Lower.lowerBlock loop pre want (.mk scope statements value) (lowerEnv typingEnv.mod typingEnv.vars results) before).1 ≠ .pending)) ∧
      VisibleSlotsReady typingEnv state) ∧
      EmitsOnly (ReadyCallObservations module func state) before
        (Lower.lowerBlock loop pre want (.mk scope statements value) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  obtain ⟨_, declared, output, statementStart, valueStart, declaration, checked, valueSource⟩ := tyBlock_checked_children source
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let entered := (emitEffect (.enter scope) env before).2
  let pushed := { entered with stack := scope :: entered.stack }
  let initialized := (Lower.initSlots pre env pushed).2
  let executed := (lowerStmts loop statements env initialized).2
  let evaluated := Lower.lowerBlockValue want value env executed
  let left := (emitEffect (.leave scope) env evaluated.2).2
  have finalExtension : left.Ext (Lower.lowerBlock loop pre want (.mk scope statements value) env before).2 :=
    LS.Ext.refl left
  have leftExtension : left.Ext completed := finalExtension.trans extension
  have valueAdvance : executed.Adv evaluated.2 := advB_lowerBlockValue want value env executed _ _ rfl
  have leaveAdvance : evaluated.2.Adv left := advB_emitEffect (.leave scope) env evaluated.2 _ _ rfl
  have valueExtension : evaluated.2.Ext completed := leaveAdvance.ext.trans leftExtension
  have executedExtension : executed.Ext completed := valueAdvance.ext.trans valueExtension
  have leftAllocated : left.vals.size ≤ completed.vals.size := allocated
  have valueAllocated : evaluated.2.vals.size ≤ completed.vals.size := Nat.le_trans leaveAdvance.vals leftAllocated
  have executedAllocated : executed.vals.size ≤ completed.vals.size := Nat.le_trans valueAdvance.vals valueAllocated
  have leftNative : SummaryPreservation.NativeRows types left := native
  have valueNative : SummaryPreservation.NativeRows types evaluated.2 :=
    leftNative.of_prefix (types_emitEffect (.leave scope) env evaluated.2 _ _ rfl)
  have executedNative : SummaryPreservation.NativeRows types executed :=
    valueNative.of_prefix (types_lowerBlockValue want value env executed _ _ rfl)
  have enteredGenerated : GeneratedBuilderState entered := generated.emitEffect (.enter scope) (env := env) rfl
  have pushedGenerated : GeneratedBuilderState pushed :=
    ⟨enteredGenerated.dense, enteredGenerated.live, enteredGenerated.targets⟩
  have initializedGenerated : GeneratedBuilderState initialized := pushedGenerated.initSlots pre (env := env) rfl
  have initializedTargets : LoopBuilderTargets loop initialized := targets.mono (Nat.le_trans
    (advB_emitEffect (.enter scope) env before _ _ rfl).ext.1 (advB_initSlots pre env pushed _ _ rfl).ext.1)
  have executedGenerated : GeneratedBuilderState executed := initializedGenerated.lowerStmts loop statements initializedTargets rfl
  have initializedExtension : initialized.Ext completed :=
    (advB_lowerStmts loop statements env initialized _ _ rfl).ext.trans executedExtension
  have initializedReady := frame.initSlots (show Lower.initSlots pre env pushed = ((), initialized) from rfl)
    initializedExtension pushedGenerated.live preSlots (by
      intro live slot input origin member
      exact preReady ((dead_emitEffect (.enter scope)).live_before rfl live) slot input origin member)
  have declaredReady : initialized.cur.isSome = true → VisibleSlotsReady declared state := by
    intro live
    exact visible.declarePre declaration (by
      intro slot type member
      obtain ⟨input, origin, bound⟩ := preCorrespondence slot type member
      exact initializedReady.2 live slot input origin bound)
  have statementPair := statementsChild declared output statementStart valueStart declaration checked
    initializedGenerated initializedTargets executedNative executedExtension executedAllocated declaredReady counter
  have valuePair : ∀ expression, value = some expression →
      ValueReadyAt state (lowerExpr expression) env executed ∧
      EmitsOnly (ReadyCallObservations module func state) executed (lowerExpr expression env executed).2 := by
    intro expression expressionRow
    have typed : Core.tyExpr output expression valueStart = .ok (type, finish) := by
      subst value
      exact valueSource
    have actual : evaluated = lowerExpr expression env executed := by
      simp only [evaluated, expressionRow, Lower.lowerBlockValue]
    exact valueChild declared output statementStart valueStart expression declaration checked expressionRow typed
      executedGenerated (by simpa only [actual] using valueNative)
      (by simpa only [actual] using valueExtension) (by simpa only [actual] using valueAllocated) statementPair.1.2
  refine ⟨?_, observation_block loop pre want scope statements value statementPair.2
    (observation_blockValue want value (fun expression row => (valuePair expression row).2))⟩
  exact frame.lowerBlock declaration checked visible preCorrespondence generated.live extension preSlots preReady
    (fun _ => statementPair.1)
    (fun _ => frame.lowerBlockValue valueExtension valueAllocated executedGenerated.live
      (fun expression row => (valuePair expression row).1))

end Goose.Lower.Validation.ReplacementContentFlowSource
