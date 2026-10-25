import Goose.Lower.Validation.SourceReadyControlJoin

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.ifValue {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {condition : ValueId} {yes no : B ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (conditionReady : before.cur.isSome = true → flowAt state.values condition ≠ .pending)
    (children : before.cur.isSome = true →
      let forked := fork condition env before
      let startedT := { forked.2 with cur := some forked.1.1 }
      let evaluatedT := yes env startedT
      let startedF := { evaluatedT.2 with cur := some forked.1.2 }
      ValueReadyAt state yes env startedT ∧ ValueReadyAt state no env startedF ∧
        LiveBound evaluatedT.2 ∧ LiveBound (no env startedF).2)
    (extension : ((whenLive 0 fun _ => do
      let (tb, eb) ← fork condition
      setCur (some tb)
      let valueT ← yes
      let endT ← curBlock
      setCur (some eb)
      let valueF ← no
      let endF ← curBlock
      Goose.Lower.joinValue endT valueT endF valueF) env before).2.Ext completed)
    (allocated : before.cur.isSome = true →
      let forked := fork condition env before
      let evaluatedT := yes env { forked.2 with cur := some forked.1.1 }
      let evaluatedF := no env { evaluatedT.2 with cur := some forked.1.2 }
      (evaluatedT.2.cur.isSome || evaluatedF.2.cur.isSome) = true →
        evaluatedF.2.vals.size < completed.vals.size) :
    ValueReadyAt state (whenLive 0 fun _ => do
      let (tb, eb) ← fork condition
      setCur (some tb)
      let valueT ← yes
      let endT ← curBlock
      setCur (some eb)
      let valueF ← no
      let endF ← curBlock
      Goose.Lower.joinValue endT valueT endF valueF) env before := by
  cases current : before.cur with
  | none =>
    simp only [ValueReadyAt, whenLive_none _ _ _ current]
    exact ⟨.refl _ _, by simp [current]⟩
  | some block =>
    have live : before.cur.isSome = true := by simp [current]
    let forked := fork condition env before
    let startedT := { forked.2 with cur := some forked.1.1 }
    let evaluatedT := yes env startedT
    let startedF := { evaluatedT.2 with cur := some forked.1.2 }
    let evaluatedF := no env startedF
    obtain ⟨yesReady, noReady, yesBound, noBound⟩ := children live
    have joined := frame.joinValue (before := evaluatedF.2) (env := env)
      (yes := evaluatedT.2.cur) (no := evaluatedF.2.cur)
      (yesValue := evaluatedT.1) (noValue := evaluatedF.1)
      (by simpa only [whenLive_some _ _ _ current, bind_run, setCur_run, curBlock_run,
        forked, startedT, evaluatedT, startedF, evaluatedF] using extension)
      (allocated live)
      (by
        intro target row
        have firstBound := yesBound target row
        exact Nat.lt_of_lt_of_le firstBound noReady.1.blocks)
      noBound yesReady.2 noReady.2
    refine ⟨?_, ?_⟩
    · have forkReady := ready_fork (env := env) conditionReady
      have startedReady : EmitsOnly (ReadyOperands state) forked.2 startedT := .of_blocks rfl
      have secondStartReady : EmitsOnly (ReadyOperands state) evaluatedT.2 startedF := .of_blocks rfl
      have emissions := forkReady.trans (startedReady.trans (yesReady.1.trans
        (secondStartReady.trans (noReady.1.trans joined.1))))
      simpa only [whenLive_some _ _ _ current, bind_run, setCur_run, curBlock_run,
        forked, startedT, evaluatedT, startedF, evaluatedF] using emissions
    · simpa only [whenLive_some _ _ _ current, bind_run, setCur_run, curBlock_run,
        forked, startedT, evaluatedT, startedF, evaluatedF] using joined.2

theorem ready_ifArms {state : State} {env : LEnv} {before : LS}
    {condition : ValueId} {yes no : B ValueId}
    (conditionReady : before.cur.isSome = true → flowAt state.values condition ≠ .pending)
    (children : before.cur.isSome = true →
      let forked := fork condition env before
      let startedT := { forked.2 with cur := some forked.1.1 }
      let evaluatedT := yes env startedT
      let startedF := { evaluatedT.2 with cur := some forked.1.2 }
      EmitsOnly (ReadyOperands state) startedT evaluatedT.2 ∧
        EmitsOnly (ReadyOperands state) startedF (no env startedF).2) :
    EmitsOnly (ReadyOperands state) before ((whenLive () fun _ => do
      let (tb, eb) ← fork condition
      setCur (some tb)
      let _ ← yes
      let endT ← curBlock
      setCur (some eb)
      let _ ← no
      let endF ← curBlock
      joinArms endT endF) env before).2 := by
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ _ current]
    exact .refl _ _
  | some block =>
    have live : before.cur.isSome = true := by simp [current]
    let forked := fork condition env before
    let startedT := { forked.2 with cur := some forked.1.1 }
    let evaluatedT := yes env startedT
    let startedF := { evaluatedT.2 with cur := some forked.1.2 }
    let evaluatedF := no env startedF
    obtain ⟨yesReady, noReady⟩ := children live
    have forkReady := ready_fork (env := env) conditionReady
    have startedReady : EmitsOnly (ReadyOperands state) forked.2 startedT := .of_blocks rfl
    have secondStartReady : EmitsOnly (ReadyOperands state) evaluatedT.2 startedF := .of_blocks rfl
    have joined := ready_joinArms state env evaluatedF.2 evaluatedT.2.cur evaluatedF.2.cur
    have emissions := forkReady.trans (startedReady.trans (yesReady.trans
      (secondStartReady.trans (noReady.trans joined))))
    simpa only [whenLive_some _ _ _ current, bind_run, setCur_run, curBlock_run,
      forked, startedT, evaluatedT, startedF, evaluatedF] using emissions

theorem ready_ifThen {state : State} {env : LEnv} {before : LS}
    {condition : ValueId} {body : B ValueId}
    (conditionReady : before.cur.isSome = true → flowAt state.values condition ≠ .pending)
    (child : before.cur.isSome = true →
      let forked := fork condition env before
      let started := { forked.2 with cur := some forked.1.1 }
      EmitsOnly (ReadyOperands state) started (body env started).2) :
    EmitsOnly (ReadyOperands state) before ((whenLive () fun _ => do
      let (tb, xb) ← fork condition
      setCur (some tb)
      let _ ← body
      emitTerm (.br xb [])
      setCur (some xb)) env before).2 := by
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ _ current]
    exact .refl _ _
  | some block =>
    have live : before.cur.isSome = true := by simp [current]
    let forked := fork condition env before
    let started := { forked.2 with cur := some forked.1.1 }
    let evaluated := body env started
    let closed := (emitTerm (.br forked.1.2 []) env evaluated.2).2
    have forkReady := ready_fork (env := env) conditionReady
    have startedReady : EmitsOnly (ReadyOperands state) forked.2 started := .of_blocks rfl
    have closedReady : EmitsOnly (ReadyOperands state) evaluated.2 closed := ready_emitTerm rfl (by
      intro _ value member
      simp [Inst.uses, Term.uses] at member)
    have finalReady : EmitsOnly (ReadyOperands state) closed { closed with cur := some forked.1.2 } := .of_blocks rfl
    simpa only [whenLive_some _ _ _ current, bind_run, setCur_run, pure_run,
      forked, started, evaluated, closed] using
      forkReady.trans (startedReady.trans ((child live).trans (closedReady.trans finalReady)))

#print axioms ready_ifArms
#print axioms ready_ifThen

#print axioms SourceReadyFrame.ifValue

end Goose.Lower.Validation.ReplacementContentFlowSource
