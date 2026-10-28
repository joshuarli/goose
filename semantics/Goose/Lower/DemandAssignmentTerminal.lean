import Goose.Lower.DemandFieldAssignmentPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem ScalarAssignmentPrefixCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint} (cursor : ScalarAssignmentPrefixCursor cx results source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  cases cursor with
  | destination child canonical demanded step =>
    obtain ⟨next, step⟩ := step
    exact (maximal next (step fuel)).elim
  | value child canonical aliases demanded progress =>
    cases progress with
    | inl instruction =>
      obtain ⟨id, op, instruction⟩ := instruction
      cases instruction.symm.trans terminal
    | inr step =>
      obtain ⟨next, step⟩ := step
      exact (maximal next (step fuel)).elim
  | store child canonical aliases site demanded =>
    cases site.instruction.symm.trans terminal

theorem FieldAssignmentPrefixCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint} (cursor : FieldAssignmentPrefixCursor cx results source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  cases cursor with
  | scalar cursor => exact cursor.excludes_maximal_terminal terminal maximal
  | address child canonical frame step =>
    obtain ⟨next, step⟩ := step
    exact (maximal next (step fuel)).elim

#print axioms ScalarAssignmentPrefixCursor.excludes_maximal_terminal
#print axioms FieldAssignmentPrefixCursor.excludes_maximal_terminal
end Goose.Lower
