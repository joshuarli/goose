import Goose.GIR.ReplacementContentFlowProofsRefinement
import Goose.GIR.ReplacementContentFlowProofsSupportStart

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

def VisibleSlotsReady (env : TEnv) (state : State) : Prop :=
  ∀ varId ∈ env.visible, ∀ localVar, env.vars[varId]? = some localVar → localVar.ty.isRefLike = true →
    flowAt state.slots varId ≠ .pending

theorem VisibleSlotsReady.empty {env : TEnv} {state : State} (empty : env.visible = []) :
    VisibleSlotsReady env state := by
  intro varId member
  simp [empty] at member

theorem VisibleSlotsReady.restrict {before after : TEnv} {state : State}
    (ready : VisibleSlotsReady before state) (variables : after.vars = before.vars)
    (visible : after.visible ⊆ before.visible) : VisibleSlotsReady after state := by
  intro varId member localVar row reference
  exact ready varId (visible member) localVar (by simpa only [variables] using row) reference

theorem VisibleSlotsReady.expression {env : TEnv} {state : State}
    (ready : VisibleSlotsReady env state) : VisibleSlotsReady (Core.exprEnv env) state := ready

theorem VisibleSlotsReady.of_extends {env : TEnv} {before after : State}
    (growth : before.Extends after) (ready : VisibleSlotsReady env before) :
    VisibleSlotsReady env after := by
  intro varId member localVar row reference
  exact (growth.slots.values varId).ready (ready varId member localVar row reference)

theorem returned_ready_of_initial_extends {func : Func} {types : Array (Option VTy)} {state : State}
    (growth : (start func types).Extends state) : state.returned ≠ .pending := by
  exact growth.returned.ready (by rw [start_returned]; simp)

theorem refReady_of_operands {types : Array (Option VTy)} {state : State} {instruction : Inst}
    (typed : ∀ value ∈ instruction.uses, ∃ type, types[value]? = some (some type))
    (ready : ∀ value ∈ instruction.uses, valRefLike types value = true → flowAt state.values value ≠ .pending) :
    refReady types state instruction = true := by
  unfold refReady
  apply List.all_eq_true.mpr
  intro value member
  obtain ⟨type, row⟩ := typed value member
  rw [row]
  by_cases reference : type.refLike = true
  · have available := ready value member (by simp [valRefLike, row, reference])
    cases actual : flowAt state.values value with
    | pending => exact False.elim (available actual)
    | unknown => simp [reference]
    | known atoms => simp [reference]
  · simp [reference]

#print axioms VisibleSlotsReady.of_extends
#print axioms returned_ready_of_initial_extends
#print axioms refReady_of_operands

end Goose.Lower.Validation.ReplacementContentFlowSource
