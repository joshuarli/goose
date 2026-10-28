import Goose.Lower.DemandFieldAssignmentPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

def AssignmentValueDemand {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    (statement : Stmt) (map : RetainedSsaMap) (before : LS) (runtime : DemandRuntimePoint) : Prop :=
  ∃ (place : Place) (expression : Expr) (origin : OriginId) (after : St)
      (child : ExprSource cfg env expression after) (aliases : List RetainedAlias),
    statement = .assign place expression origin ∧
    CanonicalExpressionDemand (map.addValues (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1 aliases) cx child runtime

theorem ScalarAssignmentPrefixCursor.maximal_terminal_at_value {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint} (cursor : ScalarAssignmentPrefixCursor cx results source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : AssignmentValueDemand (cfg := cfg) (env := env) (cx := cx) (results := results) statement map before runtime := by
  cases cursor with
  | destination child canonical demanded step =>
    obtain ⟨next, step⟩ := step
    exact (maximal next (step fuel)).elim
  | value child canonical aliases demanded =>
    exact ⟨_, _, _, _, child, aliases, rfl, demanded⟩
  | store child canonical aliases site demanded =>
    cases site.instruction.symm.trans terminal

theorem FieldAssignmentPrefixCursor.maximal_terminal_at_value {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint} (cursor : FieldAssignmentPrefixCursor cx results source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : AssignmentValueDemand (cfg := cfg) (env := env) (cx := cx) (results := results) statement map before runtime := by
  cases cursor with
  | scalar cursor => exact cursor.maximal_terminal_at_value terminal maximal
  | address child canonical frame step =>
    obtain ⟨next, step⟩ := step
    exact (maximal next (step fuel)).elim

#print axioms ScalarAssignmentPrefixCursor.maximal_terminal_at_value
#print axioms FieldAssignmentPrefixCursor.maximal_terminal_at_value
end Goose.Lower
