import Goose.Lower.Validation.ReplacementContentFlowSourceReadyEmit

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem ready_emitEffect {state : State} {before after : LS} {env : LEnv} {result : Unit} {effect : Effect}
    (run : emitEffect effect env before = (result, after))
    (operands : before.cur.isSome = true → ∀ operand ∈ effect.uses,
      flowAt state.values operand ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after := by
  cases current : before.cur with
  | none =>
    rw [emitEffect_none _ _ current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .refl _ _
  | some block =>
    exact emitsOnly_emitEffect effect (by
      constructor
      · exact operands (by simp [current])
      · simp [loadedResults]) env before result after run

theorem ready_emitTerm {state : State} {before after : LS} {env : LEnv} {result : Unit} {term : Term}
    (run : emitTerm term env before = (result, after))
    (operands : before.cur.isSome = true → ∀ operand ∈ term.uses,
      flowAt state.values operand ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after := by
  cases current : before.cur with
  | none =>
    rw [emitTerm_none _ _ current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .refl _ _
  | some block =>
    exact emitsOnly_emitTerm term (by
      constructor
      · exact operands (by simp [current])
      · simp [loadedResults]) env before result after run

#print axioms ready_emitEffect
#print axioms ready_emitTerm

end Goose.Lower.Validation.ReplacementContentFlowSource
