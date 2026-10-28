import Goose.Lower.DemandNestedCallLoopDepth
import Goose.Lower.DemandWhileCallCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive NestedCallLoopCursorStep {cfg : Cfg} (caller : Func) (results : List Ty) {root : DemandNode} {owner : Nat}
    (inner : ∀ {env : Env} (loop : Option LoopCtx),
      GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner →
      ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
        LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) :
    ∀ {env : Env} (loop : Option LoopCtx)
      (_selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner),
      ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
        LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | mixed {env : Env} {loop : Option LoopCtx} {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
      {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ReachableScalarCallCursor caller results loop source before built initial start map required runtime) :
      NestedCallLoopCursorStep caller results inner loop selected source before built initial start map required runtime
  | existing {env : Env} {loop : Option LoopCtx} {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
      {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileCallStatementCursor caller results selected source before built initial start map required runtime) :
      NestedCallLoopCursorStep caller results inner loop selected source before built initial start map required runtime
  | conditional {env : Env} {loop : Option LoopCtx} {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
      {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : RecursiveLoopIfCursorStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
        (fun {_innerEnv} innerSelected {_innerStatement} {_innerState} innerSource innerBefore innerBuilt innerInitial innerStart innerMap innerRequired innerRuntime =>
          inner loop innerSelected innerSource innerBefore innerBuilt innerInitial innerStart innerMap innerRequired innerRuntime)
        selected source before built initial start map required runtime) :
      NestedCallLoopCursorStep caller results inner loop selected source before built initial start map required runtime
  | body {env : Env} {loop : Option LoopCtx} {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
      {condition : Expr} {body : Core.Block} {origin : OriginId} {state current middle : St} {count : Nat}
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
        (@inner { env with scopes := (body.scope, middle.nextScope) :: env.scopes }
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩) selected)
        (GeneratedBranchBlockEffectDemand branch map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results branchStart
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
          conditionFrame) runtime) :
      NestedCallLoopCursorStep caller results inner loop selected source before built initial start map required runtime

def NestedCallLoopCursor {cfg : Cfg} (caller : Func) (results : List Ty) {root : DemandNode} {owner : Nat}
    (depth : Nat) {env : Env} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
    (before built : LS) (initial : GIR.Frame) (start : Pt) (map required : RetainedSsaMap) (runtime : DemandRuntimePoint) : Prop :=
  match depth with
  | 0 => ReachableScalarCallCursor caller results loop source before built initial start map required runtime
  | depth + 1 => NestedCallLoopCursorStep caller results
      (fun {_innerEnv} innerLoop innerSelected {_innerStatement} {_innerState} innerSource innerBefore innerBuilt innerInitial innerStart innerMap innerRequired innerRuntime =>
        NestedCallLoopCursor caller results depth innerLoop innerSelected innerSource innerBefore innerBuilt innerInitial innerStart innerMap innerRequired innerRuntime)
      loop selected source before built initial start map required runtime

theorem NestedCallLoopCursor.succ {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat} {loop : Option LoopCtx} (depth : Nat)
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : NestedCallLoopCursor caller results depth loop selected source before built initial start map required runtime) :
    NestedCallLoopCursor caller results (depth + 1) loop selected source before built initial start map required runtime := by
  induction depth generalizing env loop statement state before built initial start map required runtime with
  | zero => exact .mixed cursor
  | succ depth ih =>
    cases cursor with
    | mixed cursor => exact .mixed cursor
    | existing cursor => exact .existing cursor
    | conditional cursor =>
      apply NestedCallLoopCursorStep.conditional
      cases cursor with
      | scalar cursor => exact .scalar cursor
      | condition child canonical demanded progress => exact .condition child canonical demanded progress
      | fork child boolean fuel canonical evaluated boundary step => exact .fork child boolean fuel canonical evaluated boundary step
      | join joinBlock fuel evaluated step post => exact .join joinBlock fuel evaluated step post
      | branch child boolean fuel conditionCanonical evaluated indexEq found branch canonical demanded =>
        apply RecursiveLoopIfCursorStep.branch child boolean fuel conditionCanonical evaluated indexEq found branch canonical
        apply demanded.mapCursor
        intro statement innerState source before built initial start map required runtime cursor
        exact ih cursor
    | body iterations active world child fuel conditionCanonical evaluated branch canonical demanded =>
      apply NestedCallLoopCursorStep.body iterations active world child fuel conditionCanonical evaluated branch canonical
      apply demanded.mapCursor
      intro statement innerState source before built initial start map required runtime cursor
      exact ih cursor

#print axioms NestedCallLoopCursor.succ

theorem NestedCallLoopCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat} {loop : Option LoopCtx} (depth : Nat)
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : NestedCallLoopCursor caller results depth loop selected source before built initial start map required runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  induction depth generalizing env loop statement state before built initial start map required runtime term fuel with
  | zero => exact ReachableScalarCallCursor.excludes_maximal_terminal cursor terminal maximal
  | succ depth ih =>
    cases cursor with
    | mixed cursor => exact cursor.excludes_maximal_terminal terminal maximal
    | existing cursor => exact cursor.excludes_maximal_terminal terminal maximal
    | conditional cursor =>
      cases cursor with
      | scalar cursor => exact ScalarAssignmentStatementPrefixCursor.excludes_maximal_terminal cursor terminal maximal
      | condition child canonical demanded progress =>
        rcases progress with ⟨id, op, instruction⟩ | ⟨next, step⟩
        · cases instruction.symm.trans terminal
        · exact maximal next (step fuel)
      | fork child boolean sourceFuel canonical evaluated boundary step =>
        obtain ⟨next, step⟩ := step
        exact maximal next (step fuel)
      | join joinBlock sourceFuel evaluated step post => exact maximal _ (step fuel)
      | branch child boolean sourceFuel conditionCanonical evaluated indexEq found branch canonical demanded =>
        apply demanded.excludes_maximal_terminal ?_ terminal maximal
        intro statement innerState source before built initial start map required runtime cursor term terminal fuel maximal
        exact ih cursor terminal maximal
    | body iterations active world child sourceFuel conditionCanonical evaluated branch canonical demanded =>
      apply demanded.excludes_maximal_terminal ?_ terminal maximal
      intro statement innerState source before built initial start map required runtime cursor term terminal fuel maximal
      exact ih cursor terminal maximal

#print axioms NestedCallLoopCursor.excludes_maximal_terminal
end Goose.Lower
