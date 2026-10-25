import Goose.Lower.Validation.ReplacementContentFlowSourceReadyBuilder
import Goose.Lower.Validation.SourceReadyObservations

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem finishFunction_emitsOnly {property : Inst → Prop}
    (impl : Impl) (value : ValueId) (env : LEnv) (before : LS)
    (returned : property (.term (.ret (if impl.body.value.isSome then [value] else []) none)))
    (branch : ∀ target, property (.term (.br target []))) :
    EmitsOnly property before (finishFunction impl value env before).2 := by
  change EmitsOnly property before ((if before.cur.isSome then
    if !impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges env.mod.noReturn then do
      let (sink, _) ← newBlock []
      emitTerm (.br sink [])
      setCur (some sink)
      emitTerm (.br sink [])
    else emitTerm (.ret (if impl.body.value.isSome then [value] else []) none)
    else pure ()) env before).2
  split
  · split
    · let created := newBlock [] env before
      let first := (emitTerm (.br created.1.1 []) env created.2).2
      let selected := { first with cur := some created.1.1 }
      have new : EmitsOnly property before created.2 :=
        (EmitsOnly.newBlock before []).trans (.of_blocks rfl)
      change EmitsOnly property before (emitTerm (.br created.1.1 []) env selected).2
      exact ((new.trans (emitsOnly_emitTerm _ (branch created.1.1) env created.2 _ _ rfl)).trans
        (show EmitsOnly property first selected from .of_blocks rfl)).trans
        (emitsOnly_emitTerm _ (branch created.1.1) env selected _ _ rfl)
    · exact emitsOnly_emitTerm _ returned env before _ _ rfl
  · exact .refl _ _

theorem finishFunction_ready {module : GIR.Module} {func : Func} {state : State}
    (impl : Impl) (value : ValueId) (env : LEnv) (before : LS)
    (ready : before.cur.isSome = true → impl.body.value.isSome = true → flowAt state.values value ≠ .pending) :
    EmitsOnly (ReadyOperands state) before (finishFunction impl value env before).2 ∧
      EmitsOnly (ReadyCallObservations module func state) before (finishFunction impl value env before).2 := by
  cases current : before.cur with
  | none =>
    have stopped : finishFunction impl value env before = ((), before) := by
      change ((if before.cur.isSome then _ else (pure () : B Unit)) env before) = ((), before)
      simp only [current, Option.isSome_none, Bool.false_eq_true, reduceIte, pure_run]
    rw [stopped]
    exact ⟨.refl _ _, .refl _ _⟩
  | some block =>
    constructor
    · apply finishFunction_emitsOnly
      · unfold ReadyOperands
        constructor
        · intro input member
          by_cases present : impl.body.value.isSome = true
          · have same : input = value := by simpa [present, Inst.uses, Term.uses] using member
            exact same ▸ ready (by simp [current]) present
          · simp [present, Inst.uses, Term.uses] at member
        · simp [loadedResults]
      · intro target
        unfold ReadyOperands
        constructor
        · intro input member
          simp [Inst.uses, Term.uses] at member
        · simp [loadedResults]
    · exact finishFunction_emitsOnly impl value env before (ReadyCallObservations.term module func state _) (fun _ => ReadyCallObservations.term module func state _)
#print axioms finishFunction_ready

end Goose.Lower.Validation.ReplacementContentFlowSource
