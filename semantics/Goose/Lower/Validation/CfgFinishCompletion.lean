import Goose.Lower.Validation.CfgCompleteHeader
import Goose.Lower.Finish

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem open_finishFunction (impl : Core.Impl) (value : ValueId) : OpenAction (finishFunction impl value) := by
  refine ⟨advB_finishFunction impl value, ?_⟩
  intro env before result after run paths bounded
  cases current : before.cur with
  | none =>
    simp only [finishFunction, bind_run, read_apply, isLive_none current, Bool.false_eq_true,
      ite_false, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact paths
  | some source =>
    simp only [finishFunction, bind_run, read_apply, isLive_run current, ite_true] at run
    change ((if !impl.results.isEmpty && impl.body.value.isNone &&
        Core.Block.diverges env.mod.noReturn impl.body then
      (do
        let (sink, _) ← newBlock []
        emitTerm (.br sink [])
        setCur (some sink)
        emitTerm (.br sink []) : B Unit)
      else emitTerm (.ret (if impl.body.value.isSome then [value] else []) none)) env before) =
        (result, after) at run
    cases synthetic : (!impl.results.isEmpty && impl.body.value.isNone &&
        Core.Block.diverges env.mod.noReturn impl.body) with
    | false =>
      simp only [synthetic, Bool.false_eq_true, ite_false] at run
      exact opens_emitTerm _ env before result after run paths bounded
    | true =>
      simp only [synthetic, ite_true] at run
      exact opens_header0 (tail := fun sink => emitTerm (.br sink []))
        (fun _ => (open_emitTerm _).live) env before result after run paths bounded (by simp [current])

theorem complete_finishFunction (impl : Core.Impl) (value : ValueId) :
    CompletionAction (finishFunction impl value) := by
  refine ⟨open_finishFunction impl value, ?_⟩
  intro env before result after run openBefore shapedBefore
  cases current : before.cur with
  | none =>
    simp only [finishFunction, bind_run, read_apply, isLive_none current, Bool.false_eq_true,
      ite_false, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨shapedBefore, rfl⟩
  | some source =>
    simp only [finishFunction, bind_run, read_apply, isLive_run current, ite_true] at run
    change ((if !impl.results.isEmpty && impl.body.value.isNone &&
        Core.Block.diverges env.mod.noReturn impl.body then
      (do
        let (sink, _) ← newBlock []
        emitTerm (.br sink [])
        setCur (some sink)
        emitTerm (.br sink []) : B Unit)
      else emitTerm (.ret (if impl.body.value.isSome then [value] else []) none)) env before) =
        (result, after) at run
    cases synthetic : (!impl.results.isEmpty && impl.body.value.isNone &&
        Core.Block.diverges env.mod.noReturn impl.body) with
    | false =>
      simp only [synthetic, Bool.false_eq_true, ite_false] at run
      exact (complete_emitTerm _).complete env before result after run openBefore shapedBefore
    | true =>
      simp only [synthetic, ite_true] at run
      exact complete_header [] [] (tail := fun sink _ => emitTerm (.br sink []))
        (fun _ _ => (complete_emitTerm _).complete)
        env before result after run openBefore shapedBefore (by simp [current])

theorem emitTerm_stopped (term : Term) (env : LEnv) (state : LS) :
    (emitTerm term env state).2.cur = none := by
  cases current : state.cur with
  | none => rw [emitTerm_none term env current]; exact current
  | some block => rw [emitTerm_run term env current]

theorem finishFunction_stopped (impl : Core.Impl) (value : ValueId) (env : LEnv) (state : LS) :
    (finishFunction impl value env state).2.cur = none := by
  cases current : state.cur with
  | none =>
    simp only [finishFunction, bind_run, read_apply, isLive_none current, Bool.false_eq_true,
      ite_false, pure_run]
    exact current
  | some block =>
    simp only [finishFunction, bind_run, read_apply, isLive_run current, ite_true]
    change ((if !impl.results.isEmpty && impl.body.value.isNone &&
        Core.Block.diverges env.mod.noReturn impl.body then
      (do
        let (sink, _) ← newBlock []
        emitTerm (.br sink [])
        setCur (some sink)
        emitTerm (.br sink []) : B Unit)
      else emitTerm (.ret (if impl.body.value.isSome then [value] else []) none)) env state).2.cur = none
    split
    · simp only [bind_run, newBlock0_run, setCur_run]
      exact emitTerm_stopped _ _ _
    · exact emitTerm_stopped _ _ _

theorem finishFunction_allClosed {impl : Core.Impl} {value : ValueId} {env : LEnv} {state : LS}
    (openState : CurrentOpen state) (shaped : ShapedBlocks state)
    (count : OpenCount state = LiveCount state) :
    AllClosed (finishFunction impl value env state).2 :=
  (complete_finishFunction impl value).closed rfl openState shaped count
    (finishFunction_stopped impl value env state)

end Goose.Lower.Validation
