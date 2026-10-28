import Goose.Lower.DemandNestedCallLoopCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive NestedCallLoopHeaderCursor {cfg : Cfg} {env : Env} (caller : Func) (results : List Ty) (depth : Nat)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | existing {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileHeaderPrefixCursor ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected
        source before built initial start map required runtime) :
      NestedCallLoopHeaderCursor caller results depth selected source before built initial start map required runtime
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
        (@NestedCallLoopCursor cfg caller results root owner depth { env with scopes := (body.scope, middle.nextScope) :: env.scopes }
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩) selected)
        (GeneratedBranchBlockEffectDemand branch map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results branchStart
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
          conditionFrame) runtime) :
      NestedCallLoopHeaderCursor caller results depth selected source before built initial start map required runtime


theorem NestedCallLoopHeaderCursor.rebase {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty} {depth : Nat}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial otherInitial : GIR.Frame} {start otherStart : Pt}
    {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : NestedCallLoopHeaderCursor caller results depth selected source before built initial start map required runtime) :
    NestedCallLoopHeaderCursor caller results depth selected source before built otherInitial otherStart map required runtime := by
  cases cursor with
  | existing cursor => exact .existing cursor.rebase
  | body iterations active world child fuel conditionCanonical evaluated branch canonical demanded =>
    exact .body iterations active world child fuel conditionCanonical evaluated branch canonical demanded

theorem NestedCallLoopHeaderCursor.toStatement {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty} {depth : Nat}
    {root : DemandNode} {owner : Nat} {loop : Option LoopCtx}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : NestedCallLoopHeaderCursor caller results depth selected source before built initial start map required runtime) :
    NestedCallLoopCursor caller results (depth + 1) loop selected source before built initial start map required runtime := by
  cases cursor with
  | existing cursor => exact .existing (.header (.existing cursor))
  | body iterations active world child fuel conditionCanonical evaluated branch canonical demanded =>
    exact .body iterations active world child fuel conditionCanonical evaluated branch canonical demanded

theorem NestedCallLoopHeaderCursor.toScalar {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : NestedCallLoopHeaderCursor caller results 0 selected source before built initial start map required runtime) :
    WhileCallHeaderCursor caller results selected source before built initial start map required runtime := by
  cases cursor with
  | existing cursor => exact .existing cursor
  | body iterations active world child fuel conditionCanonical evaluated branch canonical demanded =>
    exact .scalarBody iterations active world child fuel conditionCanonical evaluated branch canonical demanded

#print axioms NestedCallLoopHeaderCursor.rebase
#print axioms NestedCallLoopHeaderCursor.toStatement
#print axioms NestedCallLoopHeaderCursor.toScalar
end Goose.Lower
