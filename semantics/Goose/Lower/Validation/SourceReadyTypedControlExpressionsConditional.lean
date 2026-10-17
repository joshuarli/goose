import Goose.Lower.Validation.SourceReadyTypedControlExpressionsBoolean

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.typedIfExpression {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv : TEnv} {results : List Ty} {condition : Expr} {yes no : Core.Block}
    {type : Ty} {start finish : Nat}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.ifE condition yes no) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.ifE condition yes no) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.ifE condition yes no) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.ifE condition yes no) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (conditionChild : ∀ next, Core.tyExpr typingEnv condition start = .ok (.bool, next) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types (lowerExpr condition (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr condition (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr condition (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → ValueReadyAt state (lowerExpr condition) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (yesChild : ∀ next last, Core.tyBlock (Core.exprEnv typingEnv) [] yes next = .ok (type, last) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let tested := lowerExpr condition env before
      let forked := fork tested.1 env tested.2
      let selected := { forked.2 with cur := some forked.1.1 }
      tested.2.cur.isSome = true → GeneratedBuilderState selected →
      SummaryPreservation.NativeRows types (Lower.lowerBlock none [] true yes env selected).2 →
      (Lower.lowerBlock none [] true yes env selected).2.Ext completed →
      (Lower.lowerBlock none [] true yes env selected).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady (Core.exprEnv typingEnv) state →
      ValueReadyAt state (Lower.lowerBlock none [] true yes) env selected)
    (noChild : ∀ next, Core.tyBlock (Core.exprEnv typingEnv) [] no next = .ok (type, finish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let tested := lowerExpr condition env before
      let forked := fork tested.1 env tested.2
      let selectedT := { forked.2 with cur := some forked.1.1 }
      let doneT := Lower.lowerBlock none [] true yes env selectedT
      let selectedF := { doneT.2 with cur := some forked.1.2 }
      tested.2.cur.isSome = true → GeneratedBuilderState selectedF →
      SummaryPreservation.NativeRows types (Lower.lowerBlock none [] true no env selectedF).2 →
      (Lower.lowerBlock none [] true no env selectedF).2.Ext completed →
      (Lower.lowerBlock none [] true no env selectedF).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady (Core.exprEnv typingEnv) state →
      ValueReadyAt state (Lower.lowerBlock none [] true no) env selectedF) :
    ValueReadyAt state (lowerExpr (.ifE condition yes no)) (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  obtain ⟨conditionFinish, yesStart, yesFinish, conditionSource, _, yesSource, noSource⟩ :=
    tyExpr_ifE_checked_children source
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let tested := lowerExpr condition env before
  have testedGenerated : GeneratedBuilderState tested.2 := generated.lowerExpr condition rfl
  have suffixAdvance : tested.2.Adv (lowerExpr (.ifE condition yes no) env before).2 :=
    advB_ifE_core tested.1 (sourceBlockScope yes) (advB_lowerBlock none [] true yes)
      (advB_lowerBlock none [] true no) env tested.2 _ _ rfl
  have conditionNative : SummaryPreservation.NativeRows types tested.2 :=
    native.of_prefix (types_ifE_core tested.1 (sourceBlockScope yes) (types_lowerBlock none [] true yes)
      (types_lowerBlock none [] true no) env tested.2 _ _ rfl)
  have conditionReady := conditionChild conditionFinish conditionSource generated conditionNative
    (suffixAdvance.ext.trans extension) (Nat.le_trans suffixAdvance.vals allocated) visible
  let choose : B ValueId := whenLive 0 fun _ => do
    let (tb, eb) ← fork tested.1
    setCur (some tb)
    let vt ← Lower.lowerBlock none [] true yes
    let endT ← curBlock
    setCur (some eb)
    let vf ← Lower.lowerBlock none [] true no
    let endF ← curBlock
    Lower.joinValue endT vt endF vf
  cases current : tested.2.cur with
  | none =>
    have stopped : lowerExpr (.ifE condition yes no) env before = (0, tested.2) := by
      simp only [lowerExpr, bind_run]
      change (whenLive _ _ env tested.2) = _
      rw [whenLive_none _ _ _ current]
    unfold ValueReadyAt
    rw [stopped]
    exact ⟨conditionReady.1, by simp [current]⟩
  | some block =>
    have live : tested.2.cur.isSome = true := by simp [current]
    let forked := fork tested.1 env tested.2
    let selectedT := { forked.2 with cur := some forked.1.1 }
    let doneT := Lower.lowerBlock none [] true yes env selectedT
    let selectedF := { doneT.2 with cur := some forked.1.2 }
    let doneF := Lower.lowerBlock none [] true no env selectedF
    let joined := Lower.joinValue doneT.2.cur doneT.1 doneF.2.cur doneF.1 env doneF.2
    let recorded := (recordValueRootRecipe joined.1 (sourceBlockScope yes) env joined.2).2
    have recording := ready_recordValueRootRecipe_fields joined.1 (sourceBlockScope yes) env joined.2
    have actual : lowerExpr (.ifE condition yes no) env before = (joined.1, recorded) := by
      simp only [lowerExpr, bind_run]
      change (whenLive _ _ env tested.2) = _
      rw [whenLive_some _ _ _ current]
      rfl
    have recordedExtension : recorded.Ext completed := by
      rw [show recorded = (lowerExpr (.ifE condition yes no) env before).2 from (congrArg Prod.snd actual).symm]
      exact extension
    have joinedExtension : joined.2.Ext completed :=
      (advB_recordValueRootRecipe joined.1 (sourceBlockScope yes) env joined.2 _ _ rfl).ext.trans recordedExtension
    have joinedAllocated : joined.2.vals.size ≤ completed.vals.size := by
      have count := allocated
      rw [actual] at count
      change recorded.vals.size ≤ completed.vals.size at count
      rw [show recorded.vals = joined.2.vals from recording.2.1] at count
      exact count
    have joinedNative : SummaryPreservation.NativeRows types joined.2 := by
      have rows := native
      rw [actual] at rows
      exact rows.of_prefix (types_recordValueRootRecipe joined.1 (sourceBlockScope yes) env joined.2 _ _ rfl)
    have noAdvance : selectedF.Adv doneF.2 := advB_lowerBlock none [] true no env selectedF _ _ rfl
    have joinExtension : doneF.2.Ext joined.2 := (ready_joinValue_prefix env doneF.2).1
    have noExtension : doneF.2.Ext completed := joinExtension.trans joinedExtension
    have yesExtension : doneT.2.Ext completed :=
      (show doneT.2.Ext selectedF from LS.Ext.refl _).trans (noAdvance.ext.trans noExtension)
    have noAllocated : doneF.2.vals.size ≤ completed.vals.size :=
      Nat.le_trans (ready_joinValue_prefix env doneF.2).2 joinedAllocated
    have yesAllocated : doneT.2.vals.size ≤ completed.vals.size := Nat.le_trans noAdvance.vals noAllocated
    have noNative : SummaryPreservation.NativeRows types doneF.2 :=
      joinedNative.of_prefix (types_joinValue doneT.2.cur doneT.1 doneF.2.cur doneF.1 env doneF.2 _ _ rfl)
    have yesNative : SummaryPreservation.NativeRows types doneT.2 :=
      noNative.of_prefix (types_lowerBlock none [] true no env selectedF _ _ rfl)
    have forkGenerated : GeneratedBuilderState forked.2 := testedGenerated.fork tested.1 (env := env) rfl
    have targetBounds := liveBound_fork current tested.1 env
    have yesGenerated : GeneratedBuilderState selectedT := forkGenerated.setCur (some forked.1.1) (env := env)
      (by intro target row; cases row; exact targetBounds.1) rfl
    have doneTGenerated : GeneratedBuilderState doneT.2 := yesGenerated.lowerBlock none [] true yes trivial rfl
    have noGenerated : GeneratedBuilderState selectedF := doneTGenerated.setCur (some forked.1.2) (env := env)
      (by intro target row; cases row
          exact Nat.lt_of_lt_of_le targetBounds.2 (advB_lowerBlock none [] true yes env selectedT _ _ rfl).ext.1) rfl
    have doneFGenerated : GeneratedBuilderState doneF.2 := noGenerated.lowerBlock none [] true no trivial rfl
    have readyYes := yesChild yesStart yesFinish yesSource live yesGenerated yesNative yesExtension yesAllocated visible.expression
    have readyNo := noChild yesFinish noSource live noGenerated noNative noExtension noAllocated visible.expression
    have branching := frame.ifValue (yes := Lower.lowerBlock none [] true yes) (no := Lower.lowerBlock none [] true no)
      conditionReady.2 (fun _ => ⟨readyYes, readyNo, doneTGenerated.live, doneFGenerated.live⟩)
      (by
        have bare : (choose env tested.2).2 = joined.2 := by
          simp only [choose, whenLive_some _ _ _ current, bind_run, setCur_run, curBlock_run]
          rfl
        change (choose env tested.2).2.Ext completed
        rw [bare]
        exact joinedExtension) (by
        intro _
        change (doneT.2.cur.isSome || doneF.2.cur.isSome) = true → doneF.2.vals.size < completed.vals.size
        intro stillLive
        exact Nat.lt_of_lt_of_le (ready_joinValue_grows env doneF.2 stillLive) joinedAllocated)
    have bare : choose env tested.2 = joined := by
      simp only [choose, whenLive_some _ _ _ current, bind_run, setCur_run, curBlock_run]
      rfl
    have bareReady : ValueReadyAt state choose env tested.2 := branching
    unfold ValueReadyAt at bareReady ⊢
    rw [bare] at bareReady
    rw [actual]
    exact ⟨conditionReady.1.trans (bareReady.1.trans (.of_blocks recording.1)),
      fun active => bareReady.2 (by
        change recorded.cur.isSome = true at active
        rw [show recorded.cur = joined.2.cur from recording.2.2] at active
        exact active)⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
