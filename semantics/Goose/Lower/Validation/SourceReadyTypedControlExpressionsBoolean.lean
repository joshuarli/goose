import Goose.Lower.Validation.SourceReadyTypedControlExpressionsFacts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem tyExpr_boolean_checked_children {env : TEnv} {left right : Expr} {isAnd : Bool}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (if isAnd then .and left right else .or left right) start = .ok (type, finish)) :
    ∃ next, Core.tyExpr env left start = .ok (.bool, next) ∧
      Core.tyExpr env right next = .ok (.bool, finish) := by
  cases isAnd <;> simp only [Bool.false_eq_true, ite_false, ite_true, Core.tyExpr] at source
  all_goals
    obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, rightStart, leftBool, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨rightType, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, tailStart, rightBool, source⟩ := (st_bind_ok _ _ _ _).mp source
    have leftFacts := (requireBool_ok _ _ _ _).mp leftBool
    have rightFacts := (requireBool_ok _ _ _ _).mp rightBool
    have finalFacts := (st_pure_ok _ _ _).mp source
    have finalOffset : finish = tailStart := congrArg Prod.snd finalFacts
    rw [leftFacts.1] at leftSource
    have leftOffset : rightStart = leftFinish := leftFacts.2
    rw [rightFacts.1, leftOffset] at rightSource
    have same : finish = rightFinish := finalOffset.trans rightFacts.2
    rw [same]
    exact ⟨leftFinish, leftSource, rightSource⟩

theorem SourceReadyFrame.typedShortCircuit {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv : TEnv} {results : List Ty} {left right : Expr} {isAnd : Bool}
    {type : Ty} {start finish : Nat}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (if isAnd then .and left right else .or left right) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types ((do
      let condition ← lowerExpr left
      Lower.shortCircuit isAnd condition (lowerExpr right)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : ((do
      let condition ← lowerExpr left
      Lower.shortCircuit isAnd condition (lowerExpr right)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : ((do
      let condition ← lowerExpr left
      Lower.shortCircuit isAnd condition (lowerExpr right)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (leftChild : ∀ next, Core.tyExpr typingEnv left start = .ok (.bool, next) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types (lowerExpr left (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr left (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr left (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → ValueReadyAt state (lowerExpr left) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (rightChild : ∀ next, Core.tyExpr typingEnv right next = .ok (.bool, finish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let condition := lowerExpr left env before
      let forked := Lower.scFork isAnd condition.1 env condition.2
      let selected := { forked.2 with cur := some forked.1.1 }
      condition.2.cur.isSome = true → GeneratedBuilderState selected →
      SummaryPreservation.NativeRows types (lowerExpr right env selected).2 →
      (lowerExpr right env selected).2.Ext completed →
      (lowerExpr right env selected).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → ValueReadyAt state (lowerExpr right) env selected) :
    ValueReadyAt state (lowerExpr (if isAnd then .and left right else .or left right))
      (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  obtain ⟨next, leftSource, rightSource⟩ := tyExpr_boolean_checked_children source
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let condition := lowerExpr left env before
  have conditionGenerated : GeneratedBuilderState condition.2 := generated.lowerExpr left rfl
  have branchExtension : (Lower.shortCircuit isAnd condition.1 (lowerExpr right) env condition.2).2.Ext completed := extension
  have branchAllocated : (Lower.shortCircuit isAnd condition.1 (lowerExpr right) env condition.2).2.vals.size ≤ completed.vals.size := allocated
  have branchAdvance := advB_shortCircuit isAnd condition.1 (advB_lowerExpr right) env condition.2 _ _ rfl
  have conditionNative : SummaryPreservation.NativeRows types condition.2 :=
    native.of_prefix (types_shortCircuit isAnd condition.1 (types_lowerExpr right) env condition.2 _ _ rfl)
  have leftReady := leftChild next leftSource generated conditionNative
    (branchAdvance.ext.trans branchExtension) (Nat.le_trans branchAdvance.vals branchAllocated) visible
  have branching := frame.shortCircuit conditionGenerated.live (advB_lowerExpr right) leftReady.2 (by
    intro live
    obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
    let forked := Lower.scFork isAnd condition.1 env condition.2
    let selected := { forked.2 with cur := some forked.1.1 }
    let evaluated := lowerExpr right env selected
    let closed := (emitTerm (.br forked.1.2.1 [evaluated.1]) env evaluated.2).2
    have actual : (Lower.shortCircuit isAnd condition.1 (lowerExpr right) env condition.2).2 =
        { closed with cur := some forked.1.2.1 } := by
      simp only [Lower.shortCircuit, whenLive_some _ _ _ current, bind_run, setCur_run, pure_run]
      rfl
    have evaluatedExtension : evaluated.2.Ext completed :=
      (advB_emitTerm (.br forked.1.2.1 [evaluated.1]) env evaluated.2 _ _ rfl).ext.trans (by
        have final : closed.Ext (Lower.shortCircuit isAnd condition.1 (lowerExpr right) env condition.2).2 := by
          rw [actual]
          exact LS.Ext.refl closed
        exact final.trans branchExtension)
    have evaluatedAllocated : evaluated.2.vals.size ≤ completed.vals.size := by
      have final : closed.vals.size ≤ completed.vals.size := by
        simpa only [actual] using branchAllocated
      exact Nat.le_trans (advB_emitTerm (.br forked.1.2.1 [evaluated.1]) env evaluated.2 _ _ rfl).vals final
    have closedNative : SummaryPreservation.NativeRows types closed := by
      have final : SummaryPreservation.NativeRows types (Lower.shortCircuit isAnd condition.1 (lowerExpr right) env condition.2).2 := native
      rw [actual] at final
      exact final
    have evaluatedNative : SummaryPreservation.NativeRows types evaluated.2 :=
      closedNative.of_prefix (types_emitTerm (.br forked.1.2.1 [evaluated.1]) env evaluated.2 _ _ rfl)
    have forkGenerated : GeneratedBuilderState forked.2 := conditionGenerated.scFork isAnd condition.1 (env := env) rfl
    have selectedGenerated : GeneratedBuilderState selected := forkGenerated.setCur (some forked.1.1) (env := env)
      (by intro target row; cases row; exact (liveBound_scFork (state := condition.2) current isAnd condition.1 env).1) rfl
    exact rightChild next rightSource live selectedGenerated evaluatedNative evaluatedExtension evaluatedAllocated visible)
    branchExtension (by
      intro live
      exact Nat.lt_of_lt_of_le (ready_shortCircuit_grows env condition.2 live (advB_lowerExpr right)) branchAllocated)
  have ready : ValueReadyAt state (do
      let condition ← lowerExpr left
      Lower.shortCircuit isAnd condition (lowerExpr right)) env before :=
    ⟨leftReady.1.trans branching.1, branching.2⟩
  cases isAnd <;> exact ready

end Goose.Lower.Validation.ReplacementContentFlowSource
