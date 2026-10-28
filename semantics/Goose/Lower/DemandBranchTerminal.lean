import Goose.Lower.DemandAssignmentTerminal
import Goose.Lower.DemandIfRecursiveLoopCursor
import Goose.Lower.DemandWhileTerminalCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem GeneratedGenericBlockPrefixDemand.excludes_maximal_terminal
    {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    {source : BlockSource cfg env [] block state} {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame}
    {cursor : ∀ {statement : Stmt} {innerState : St}, StmtSource cfg
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } statement innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    (excludes : ∀ {statement : Stmt} {innerState : St}
      (source : StmtSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } statement innerState)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      cursor source before built initial start map required runtime → ∀ {term : Term},
      instAt cx.fn runtime.point = some (.term term) → ∀ {fuel : Nat},
      (∀ next, ¬ DemandInstructionStep cx fuel runtime next) → False)
    {runtime : DemandRuntimePoint}
    (demanded : GeneratedGenericBlockPrefixDemand source selected map required before loop initial cursor
      (GeneratedBranchBlockEffectDemand source map required cx results before loop initial) runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  cases demanded with
  | emitted demanded instruction =>
    obtain ⟨effect, instruction⟩ := instruction
    cases instruction.symm.trans terminal
  | suffix demanded =>
    obtain ⟨_, effect, instruction⟩ := demanded
    cases instruction.symm.trans terminal
  | body canonical demanded => exact demanded.excludes_maximal_terminal excludes terminal maximal

theorem RecursiveLoopIfCursor.excludes_maximal_terminal {cfg : Cfg} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} {loop : Option LoopCtx} (depth : Nat) :
    ∀ {env : Env} {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
      {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
      {runtime : DemandRuntimePoint}, RecursiveLoopIfCursor cx results loop depth selected source before built initial start map required runtime →
      ∀ {term : Term}, instAt cx.fn runtime.point = some (.term term) → ∀ {fuel : Nat},
      (∀ next, ¬ DemandInstructionStep cx fuel runtime next) → False := by
  induction depth with
  | zero =>
    intro env selected statement state source before built initial start map required runtime cursor term terminal fuel maximal
    exact ScalarAssignmentStatementPrefixCursor.excludes_maximal_terminal cursor terminal maximal
  | succ depth ih =>
    intro env selected statement state source before built initial start map required runtime cursor term terminal fuel maximal
    cases cursor with
    | scalar cursor => exact ScalarAssignmentStatementPrefixCursor.excludes_maximal_terminal cursor terminal maximal
    | condition child canonical demanded progress =>
      cases progress with
      | inl instruction =>
        obtain ⟨id, op, instruction⟩ := instruction
        cases instruction.symm.trans terminal
      | inr step =>
        obtain ⟨next, step⟩ := step
        exact maximal next (step fuel)
    | fork child boolean sourceFuel canonical evaluated boundary step =>
      obtain ⟨next, step⟩ := step
      exact maximal next (step fuel)
    | join joinBlock sourceFuel evaluated step post => exact maximal _ (step fuel)
    | branch child boolean sourceFuel conditionCanonical evaluated indexEq found branch canonical demanded =>
      apply demanded.excludes_maximal_terminal ?_ terminal maximal
      intro statement state source before built initial start map required runtime cursor term terminal fuel maximal
      exact ih cursor terminal maximal

theorem WhileStatementPrefixCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint} (cursor : WhileStatementPrefixCursor cx results selected source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  obtain ⟨condition, body, origin, current, middle, count, branchStart, headerState, header, exitBlock, conditionFrame,
    branch, statementEq, iterations, demanded⟩ := cursor.maximal_terminal_at_body terminal maximal
  apply demanded.excludes_maximal_terminal ?_ terminal maximal
  intro statement state source before built initial start map required runtime cursor term terminal fuel maximal
  exact RecursiveLoopIfCursor.excludes_maximal_terminal (Place._sizeOf_11 body.stmts) cursor terminal maximal

#print axioms GeneratedGenericBlockPrefixDemand.excludes_maximal_terminal
#print axioms RecursiveLoopIfCursor.excludes_maximal_terminal
#print axioms WhileStatementPrefixCursor.excludes_maximal_terminal
end Goose.Lower
