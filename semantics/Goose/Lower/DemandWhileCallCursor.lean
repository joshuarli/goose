import Goose.Lower.DemandWhileCallTrueBody
import Goose.Lower.DemandCallLoopTerminal

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive WhileCallHeaderCursor {cfg : Cfg} {env : Env} (caller : Func) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | existing {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileHeaderPrefixCursor ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected
        source before built initial start map required runtime) :
      WhileCallHeaderCursor caller results selected source before built initial start map required runtime
  | body {condition : Expr} {body : Core.Block} {origin : OriginId} {state current middle : St} {count : Nat}
      {source : StmtSource cfg env (.while condition body origin) state} {before built branchStart headerState : LS}
      {header exitBlock : BlockId} {initial conditionFrame : GIR.Frame} {start : Pt}
      {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (iterations : WhileIterations cfg env condition body count state current)
      (active : StmtSource cfg env (.while condition body origin) current) (world : active.world = source.world)
      (child : ExprSource cfg env condition current) (fuel : Nat)
      (conditionCanonical : active.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
      (evaluated : evalExpr fuel cfg env condition current = .ok (.bool true) middle)
      (branch : BlockSource cfg env [] body middle)
      (canonical : active.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]))
      (demanded : GeneratedGenericBlockPrefixDemand (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) branch selected map required branchStart
        (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
        conditionFrame
        (@ReachableCallStatementFamilyCursor cfg { env with scopes := (body.scope, middle.nextScope) :: env.scopes } caller results
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩))
        (GeneratedBranchBlockEffectDemand branch map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results branchStart
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
          conditionFrame) runtime) :
      WhileCallHeaderCursor caller results selected source before built initial start map required runtime

theorem WhileCallHeaderCursor.rebase {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial otherInitial : GIR.Frame} {start otherStart : Pt}
    {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : WhileCallHeaderCursor caller results selected source before built initial start map required runtime) :
    WhileCallHeaderCursor caller results selected source before built otherInitial otherStart map required runtime := by
  cases cursor with
  | existing cursor => exact .existing cursor.rebase
  | body iterations active world child fuel conditionCanonical evaluated branch canonical demanded =>
    exact .body iterations active world child fuel conditionCanonical evaluated branch canonical demanded

theorem WhileCallHeaderCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : WhileCallHeaderCursor caller results selected source before built initial start map required runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  cases cursor with
  | existing cursor => exact (WhileStatementPrefixCursor.header cursor).excludes_maximal_terminal terminal maximal
  | body iterations active world child sourceFuel conditionCanonical evaluated branch canonical demanded =>
    exact demanded.call_excludes_maximal_terminal terminal maximal

inductive WhileCallStatementCursor {cfg : Cfg} {env : Env} (caller : Func) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | entry {condition : Expr} {body : Core.Block} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.while condition body origin) state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
      (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
      (step : ∃ next, ∀ fuel, DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel ⟨start, initial, state⟩ next) :
      WhileCallStatementCursor caller results selected source before built initial start map required ⟨start, initial, state⟩
  | header {statement : Stmt} {state : St} {source : StmtSource cfg env statement state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileCallHeaderCursor caller results selected source before built initial start map required runtime) :
      WhileCallStatementCursor caller results selected source before built initial start map required runtime

theorem WhileCallStatementCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : WhileCallStatementCursor caller results selected source before built initial start map required runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  cases cursor with
  | entry realized step => obtain ⟨next, step⟩ := step; exact maximal next (step fuel)
  | header cursor => exact cursor.excludes_maximal_terminal terminal maximal

#print axioms WhileCallStatementCursor.excludes_maximal_terminal

#print axioms WhileCallHeaderCursor.rebase
#print axioms WhileCallHeaderCursor.excludes_maximal_terminal
end Goose.Lower
