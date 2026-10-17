import Goose.Lower.Validation.SourceReadyControlPrimitives

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem ready_patchBrs0 (state : State) (env : LEnv) (before : LS) (target : BlockId) (incoming : List BlockId) :
    EmitsOnly (ReadyOperands state) before (patchBrs0 target incoming env before).2 := by
  induction incoming generalizing before with
  | nil => exact .refl _ _
  | cons block rest ih =>
    have first := emitsOnly_pushInst block (.term (.br target []))
      (show ReadyOperands state _ from by
        unfold ReadyOperands
        constructor
        · intro value member
          simp [Inst.uses, Term.uses] at member
        · simp [loadedResults])
      env before _ _ rfl
    exact first.trans (ih _)

theorem ready_joinArms (state : State) (env : LEnv) (before : LS) (yes no : Option BlockId) :
    EmitsOnly (ReadyOperands state) before (joinArms yes no env before).2 := by
  unfold joinArms
  split
  · exact .of_blocks rfl
  · let created := (newBlock [] env before).2
    have newReady := emitsOnly_newBlock (ReadyOperands state) [] env before _ created rfl
    have patchedReady := ready_patchBrs0 state env created before.blocks.size (yes.toList ++ no.toList)
    exact (newReady.trans patchedReady).trans (.of_blocks rfl)

theorem SourceReadyFrame.joinValue {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {yes no : Option BlockId} {yesValue noValue : ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (Goose.Lower.joinValue yes yesValue no noValue env before).2.Ext completed)
    (allocated : (yes.isSome || no.isSome) = true → before.vals.size < completed.vals.size)
    (yesBound : ∀ block, yes = some block → block < before.blocks.size)
    (noBound : ∀ block, no = some block → block < before.blocks.size)
    (yesReady : yes.isSome = true → flowAt state.values yesValue ≠ .pending)
    (noReady : no.isSome = true → flowAt state.values noValue ≠ .pending) :
    ValueReadyAt state (Goose.Lower.joinValue yes yesValue no noValue) env before := by
  cases yes with
  | none =>
    cases no with
    | none => exact ⟨.of_blocks rfl, by simp [Goose.Lower.joinValue, bind_run, setCur_run, pure_run]⟩
    | some noBlock =>
      exact frame.joinLive (by simp) (by
        intro pair member
        have same : pair = (noBlock, noValue) := by simpa using member
        subst pair
        exact noBound noBlock rfl) (by
        intro pair member
        have same : pair = (noBlock, noValue) := by simpa using member
        subst pair
        exact noReady rfl) extension (allocated rfl)
  | some yesBlock =>
    cases no with
    | none =>
      exact frame.joinLive (by simp) (by
        intro pair member
        have same : pair = (yesBlock, yesValue) := by simpa using member
        subst pair
        exact yesBound yesBlock rfl) (by
        intro pair member
        have same : pair = (yesBlock, yesValue) := by simpa using member
        subst pair
        exact yesReady rfl) extension (allocated rfl)
    | some noBlock =>
      exact frame.joinLive (by simp) (by
        intro pair member
        rcases (show pair = (yesBlock, yesValue) ∨ pair = (noBlock, noValue) from by simpa using member) with h | h
        · subst pair; exact yesBound yesBlock rfl
        · subst pair; exact noBound noBlock rfl) (by
        intro pair member
        rcases (show pair = (yesBlock, yesValue) ∨ pair = (noBlock, noValue) from by simpa using member) with h | h
        · subst pair; exact yesReady rfl
        · subst pair; exact noReady rfl) extension (allocated rfl)

#print axioms ready_patchBrs0
#print axioms ready_joinArms
#print axioms SourceReadyFrame.joinValue

end Goose.Lower.Validation.ReplacementContentFlowSource
