import Goose.Lower.Validation.SourceReadyTypedStatementsControlFrames
import Goose.Lower.Validation.SourceReadyObservationControlStatements

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.observedTypedIfStatement {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv output : TEnv} {results : List Ty} {loop : Option LoopCtx}
    {scope start finish : Nat} {origin : OriginId} {condition : Expr} {yes : Core.Block} {no : Option Core.Block}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.ifS condition yes no origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before) (targets : LoopBuilderTargets loop before)
    (native : SummaryPreservation.NativeRows types
      (lowerStmt loop (.ifS condition yes no origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.ifS condition yes no origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.ifS condition yes no origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (counter : ∀ context header integer index, loop = some context → context.cont = .next header integer index →
      flowAt state.values index ≠ .pending)
    (conditionChild : ∀ next, Core.tyExpr typingEnv condition start = .ok (.bool, next) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types (lowerExpr condition (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr condition (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr condition (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → ValueReadyAt state (lowerExpr condition) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerExpr condition (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (yesChild : ∀ type next last initial, Core.tyBlock typingEnv [] yes next = .ok (type, last) →
      GeneratedBuilderState initial → LoopBuilderTargets loop initial →
      SummaryPreservation.NativeRows types (Lower.lowerBlock loop [] false yes (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 →
      (Lower.lowerBlock loop [] false yes (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed →
      (Lower.lowerBlock loop [] false yes (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (∀ context header integer index, loop = some context → context.cont = .next header integer index → flowAt state.values index ≠ .pending) →
      EmitsOnly (ReadyOperands state) initial (Lower.lowerBlock loop [] false yes (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 ∧
      EmitsOnly (ReadyCallObservations module func state) initial (Lower.lowerBlock loop [] false yes (lowerEnv typingEnv.mod typingEnv.vars results) initial).2)
    (noChild : ∀ body type next initial, no = some body → Core.tyBlock typingEnv [] body next = .ok (type, finish) →
      GeneratedBuilderState initial → LoopBuilderTargets loop initial →
      SummaryPreservation.NativeRows types (Lower.lowerBlock loop [] false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 →
      (Lower.lowerBlock loop [] false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed →
      (Lower.lowerBlock loop [] false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (∀ context header integer index, loop = some context → context.cont = .next header integer index → flowAt state.values index ≠ .pending) →
      EmitsOnly (ReadyOperands state) initial (Lower.lowerBlock loop [] false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 ∧
      EmitsOnly (ReadyCallObservations module func state) initial (Lower.lowerBlock loop [] false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2) :
    (EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.ifS condition yes no origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.ifS condition yes no origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before
        (lowerStmt loop (.ifS condition yes no origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  obtain ⟨next, yesType, yesFinish, conditionSource, yesSource, noSource, outputEq⟩ := tyStmt_if_children source
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let tested := lowerExpr condition env before
  have suffixAdvance : tested.2.Adv (lowerStmt loop (.ifS condition yes no origin) env before).2 := by
    cases no with
    | none => exact advB_ifS_none_core tested.1 (advB_lowerBlock loop [] false yes) env tested.2 _ _ rfl
    | some body => exact advB_ifS_some_core tested.1 (advB_lowerBlock loop [] false yes) (advB_lowerBlock loop [] false body) env tested.2 _ _ rfl
  have suffixTypes : TypePrefix tested.2 (lowerStmt loop (.ifS condition yes no origin) env before).2 := by
    cases no with
    | none => exact types_ifS_none_core tested.1 (types_lowerBlock loop [] false yes) env tested.2 _ _ rfl
    | some body => exact types_ifS_some_core tested.1 (types_lowerBlock loop [] false yes) (types_lowerBlock loop [] false body) env tested.2 _ _ rfl
  have testedGenerated : GeneratedBuilderState tested.2 := generated.lowerExpr condition rfl
  have conditionPair := conditionChild next conditionSource generated (native.of_prefix suffixTypes)
    (suffixAdvance.ext.trans extension) (Nat.le_trans suffixAdvance.vals allocated) visible
  have yesPair : ∀ type next last, Core.tyBlock typingEnv [] yes next = .ok (type, last) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let evaluated := lowerExpr condition env before
      let forked := fork evaluated.1 env evaluated.2
      let selected := { forked.2 with cur := some forked.1.1 }
      evaluated.2.cur.isSome = true → EmitsOnly (ReadyOperands state) selected (Lower.lowerBlock loop [] false yes env selected).2 ∧
      EmitsOnly (ReadyCallObservations module func state) selected (Lower.lowerBlock loop [] false yes env selected).2 := by
    intro bodyType bodyStart bodyFinish bodyChecked
    change tested.2.cur.isSome = true → _
    intro live
    obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
    let forked := fork tested.1 env tested.2
    let selected := { forked.2 with cur := some forked.1.1 }
    let doneT := Lower.lowerBlock loop [] false yes env selected
    have forkGenerated : GeneratedBuilderState forked.2 := testedGenerated.fork tested.1 (env := env) rfl
    have selectedGenerated : GeneratedBuilderState selected := forkGenerated.setCur (some forked.1.1) (env := env)
      (by intro target row; cases row; exact (liveBound_fork current tested.1 env).1) rfl
    have selectedTargets : LoopBuilderTargets loop selected := targets.mono
      (Nat.le_trans (advB_lowerExpr condition env before _ _ rfl).ext.1 (advB_fork tested.1 env tested.2 _ _ rfl).ext.1)
    have afterFacts : SummaryPreservation.NativeRows types doneT.2 ∧ doneT.2.Ext completed ∧ doneT.2.vals.size ≤ completed.vals.size := by
      cases selectedNo : no with
      | none =>
        let closed := (emitTerm (.br forked.1.2 []) env doneT.2).2
        have actual : (lowerStmt loop (.ifS condition yes no origin) env before).2 = { closed with cur := some forked.1.2 } := by
          rw [selectedNo]
          change (whenLive _ _ env tested.2).2 = _
          rw [whenLive_some _ _ _ current]
          rfl
        have finalExt : closed.Ext completed := by have h := extension; rw [actual] at h; exact h
        have finalNative : SummaryPreservation.NativeRows types closed := by have h := native; rw [actual] at h; exact h
        have finalCount : closed.vals.size ≤ completed.vals.size := by have h := allocated; rw [actual] at h; exact h
        have step := advB_emitTerm (.br forked.1.2 []) env doneT.2 _ _ rfl
        exact ⟨finalNative.of_prefix (types_emitTerm (.br forked.1.2 []) env doneT.2 _ _ rfl),
          step.ext.trans finalExt, Nat.le_trans step.vals finalCount⟩
      | some body =>
        let selectedF := { doneT.2 with cur := some forked.1.2 }
        let doneF := Lower.lowerBlock loop [] false body env selectedF
        let joined := (joinArms doneT.2.cur doneF.2.cur env doneF.2).2
        have actual : (lowerStmt loop (.ifS condition yes no origin) env before).2 = joined := by
          rw [selectedNo]
          change (whenLive _ _ env tested.2).2 = _
          rw [whenLive_some _ _ _ current]
          rfl
        have joinedExt : joined.Ext completed := actual ▸ extension
        have joinedNative : SummaryPreservation.NativeRows types joined := actual ▸ native
        have joinedCount : joined.vals.size ≤ completed.vals.size := actual ▸ allocated
        have otherStep := advB_lowerBlock loop [] false body env selectedF _ _ rfl
        have closing := ready_joinArms state env doneF.2 doneT.2.cur doneF.2.cur
        have doneFNative := joinedNative.of_prefix (types_joinArms doneT.2.cur doneF.2.cur env doneF.2 _ _ rfl)
        have doneFCount : doneF.2.vals.size ≤ completed.vals.size := by
          rw [show doneF.2.vals = joined.vals from (ready_joinArms_values _ _ _ _).symm]
          exact joinedCount
        exact ⟨doneFNative.of_prefix (types_lowerBlock loop [] false body env selectedF _ _ rfl),
          otherStep.ext.trans (closing.extension.trans joinedExt), Nat.le_trans otherStep.vals doneFCount⟩
    exact yesChild bodyType bodyStart bodyFinish selected bodyChecked selectedGenerated selectedTargets
      afterFacts.1 afterFacts.2.1 afterFacts.2.2 visible counter
  have noPair : ∀ body type next, no = some body → Core.tyBlock typingEnv [] body next = .ok (type, finish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let evaluated := lowerExpr condition env before
      let forked := fork evaluated.1 env evaluated.2
      let selectedT := { forked.2 with cur := some forked.1.1 }
      let doneT := Lower.lowerBlock loop [] false yes env selectedT
      let selectedF := { doneT.2 with cur := some forked.1.2 }
      evaluated.2.cur.isSome = true → EmitsOnly (ReadyOperands state) selectedF (Lower.lowerBlock loop [] false body env selectedF).2 ∧
      EmitsOnly (ReadyCallObservations module func state) selectedF (Lower.lowerBlock loop [] false body env selectedF).2 := by
    intro body bodyType bodyStart selectedNo bodyChecked
    change tested.2.cur.isSome = true → _
    intro live
    obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
    let forked := fork tested.1 env tested.2
    let selectedT := { forked.2 with cur := some forked.1.1 }
    let doneT := Lower.lowerBlock loop [] false yes env selectedT
    let selectedF := { doneT.2 with cur := some forked.1.2 }
    let doneF := Lower.lowerBlock loop [] false body env selectedF
    let joined := (joinArms doneT.2.cur doneF.2.cur env doneF.2).2
    have actual : (lowerStmt loop (.ifS condition yes no origin) env before).2 = joined := by
      rw [selectedNo]
      change (whenLive _ _ env tested.2).2 = _
      rw [whenLive_some _ _ _ current]
      rfl
    have joinedExt : joined.Ext completed := actual ▸ extension
    have joinedNative : SummaryPreservation.NativeRows types joined := actual ▸ native
    have joinedCount : joined.vals.size ≤ completed.vals.size := actual ▸ allocated
    have closing := ready_joinArms state env doneF.2 doneT.2.cur doneF.2.cur
    have doneFNative := joinedNative.of_prefix (types_joinArms doneT.2.cur doneF.2.cur env doneF.2 _ _ rfl)
    have doneFCount : doneF.2.vals.size ≤ completed.vals.size := by
      rw [show doneF.2.vals = joined.vals from (ready_joinArms_values _ _ _ _).symm]
      exact joinedCount
    have forkGenerated : GeneratedBuilderState forked.2 := testedGenerated.fork tested.1 (env := env) rfl
    have targetBounds := liveBound_fork current tested.1 env
    have selectedTGenerated : GeneratedBuilderState selectedT := forkGenerated.setCur (some forked.1.1) (env := env)
      (by intro target row; cases row; exact targetBounds.1) rfl
    have selectedTTargets : LoopBuilderTargets loop selectedT := targets.mono
      (Nat.le_trans (advB_lowerExpr condition env before _ _ rfl).ext.1 (advB_fork tested.1 env tested.2 _ _ rfl).ext.1)
    have doneTGenerated : GeneratedBuilderState doneT.2 := selectedTGenerated.lowerBlock loop [] false yes selectedTTargets rfl
    have yesStep := advB_lowerBlock loop [] false yes env selectedT _ _ rfl
    have selectedFGenerated : GeneratedBuilderState selectedF := doneTGenerated.setCur (some forked.1.2) (env := env)
      (by intro target row; cases row; exact Nat.lt_of_lt_of_le targetBounds.2 yesStep.ext.1) rfl
    have selectedFTargets : LoopBuilderTargets loop selectedF := selectedTTargets.mono yesStep.ext.1
    exact noChild body bodyType bodyStart selectedF selectedNo bodyChecked selectedFGenerated selectedFTargets
      doneFNative (closing.extension.trans joinedExt) doneFCount visible counter
  have semantic := typed_ready_if source visible (fun _ _ => conditionPair.1)
    (fun type next last checked live => (yesPair type next last checked live).1)
    (fun body type next row checked live => (noPair body type next row checked live).1)
  refine ⟨semantic, ?_⟩
  cases no with
  | none =>
    exact observation_ifStatement_none loop condition yes origin conditionPair.2
      (fun live => (yesPair yesType next yesFinish yesSource live).2)
  | some body =>
    obtain ⟨noType, noChecked⟩ := noSource
    exact observation_ifStatement_some loop condition yes body origin conditionPair.2
      (fun live => (yesPair yesType next yesFinish yesSource live).2)
      (fun live => (noPair body noType yesFinish rfl noChecked live).2)

end Goose.Lower.Validation.ReplacementContentFlowSource
