import Goose.Lower.DemandWhilePrefixFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

def WhileLoopBodyDemand {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (statement : Stmt) (state : St) (map required : RetainedSsaMap) (runtime : DemandRuntimePoint) : Prop :=
∃ (condition : Expr) (body : Core.Block) (origin : OriginId) (current middle : St) (count : Nat)
      (branchStart headerState : LS) (header exitBlock : BlockId) (conditionFrame : GIR.Frame)
      (branch : BlockSource cfg env [] body middle),
      statement = .while condition body origin ∧ WhileIterations cfg env condition body count state current ∧
      GeneratedGenericBlockPrefixDemand branch selected map required branchStart
        (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
        conditionFrame
        (@RecursiveLoopIfCursor cfg cx results root owner
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
          (Place._sizeOf_11 body.stmts) { env with scopes := (body.scope, middle.nextScope) :: env.scopes } selected)
        (GeneratedBranchBlockEffectDemand branch map required cx results branchStart
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
          conditionFrame) runtime

theorem WhileHeaderPrefixCursor.maximal_terminal_at_body {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt}
    {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : WhileHeaderPrefixCursor cx results selected source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term))
    {fuel : Nat} (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) :
    WhileLoopBodyDemand selected statement state map required runtime := by
  cases cursor with
  | condition iterations active world child canonical demanded progress =>
    cases progress with
    | inl instruction =>
      obtain ⟨id, op, instruction⟩ := instruction
      cases instruction.symm.trans terminal
    | inr step =>
      obtain ⟨next, step⟩ := step
      exact (maximal next (step fuel)).elim
  | fork iterations active world child boolean sourceFuel canonical evaluated boundary step =>
    obtain ⟨next, step⟩ := step
    exact (maximal next (step fuel)).elim
  | body iterations active world child sourceFuel conditionCanonical evaluated branch canonical demanded =>
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, branch, rfl, iterations, demanded⟩
  | backEdge iterations active world child conditionFuel bodyFuel conditionCanonical conditionDone branch canonical bodyDone ended step =>
    exact (maximal _ (step fuel)).elim

theorem WhileStatementPrefixCursor.maximal_terminal_at_body {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt}
    {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : WhileStatementPrefixCursor cx results selected source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term))
    {fuel : Nat} (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) :
    WhileLoopBodyDemand selected statement state map required runtime := by
  cases cursor with
  | entry realized step =>
    obtain ⟨next, step⟩ := step
    exact (maximal next (step fuel)).elim
  | header cursor => exact cursor.maximal_terminal_at_body terminal maximal

#print axioms WhileHeaderPrefixCursor.maximal_terminal_at_body
#print axioms WhileStatementPrefixCursor.maximal_terminal_at_body
end Goose.Lower
