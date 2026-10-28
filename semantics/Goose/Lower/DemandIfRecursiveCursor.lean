import Goose.Lower.DemandIfRecursiveDepth

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive RecursiveIfCursorStep {cfg : Cfg} (cx : FnCtx) (results : List Ty) {root : DemandNode} {owner : Nat}
    (inner : ∀ {env : Env}, GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner →
      ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
        LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) :
    ∀ {env : Env} (_selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner),
    ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | base {env : Env} {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
      {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : IfMixedStatementCursor cx results selected source before built initial start map required runtime) :
      RecursiveIfCursorStep cx results inner selected source before built initial start map required runtime
  | branch {env : Env} {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
      {condition : Expr} {yes : Core.Block} {no : Option Core.Block} {origin : OriginId} {state middle : St}
      {source : StmtSource cfg env (.ifS condition yes no origin) state} {block : Core.Block} {index : Nat}
      {before built branchStart : LS} {initial branchFrame : GIR.Frame} {start : Pt}
      {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env condition state) (boolean : Bool) (fuel : Nat)
      (conditionCanonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
      (evaluated : evalExpr fuel cfg env condition state = .ok (.bool boolean) middle)
      (indexEq : index = if boolean then 1 else 2)
      (found : (DemandNode.statement (.ifS condition yes no origin)).child? index = some (.block block))
      (branch : BlockSource cfg env [] block middle) (canonical : source.BlockChildAt branch index found)
      (demanded : GeneratedGenericBlockPrefixDemand branch selected map required branchStart none branchFrame
        (@inner { env with scopes := (block.scope, middle.nextScope) :: env.scopes } selected)
        (GeneratedClearBlockDemand branch map required cx results branchStart none branchFrame) runtime) :
      RecursiveIfCursorStep cx results inner selected source before built initial start map required runtime

def RecursiveIfCursor {cfg : Cfg} (cx : FnCtx) (results : List Ty) {root : DemandNode} {owner : Nat}
    (depth : Nat) {env : Env}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
    (before built : LS) (initial : GIR.Frame) (start : Pt) (map required : RetainedSsaMap) (runtime : DemandRuntimePoint) : Prop :=
  match depth with
  | 0 => ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime
  | depth + 1 => RecursiveIfCursorStep cx results
      (fun {_innerEnv} innerSelected {_innerStatement} {_innerState} innerSource innerBefore innerBuilt innerInitial innerStart innerMap innerRequired innerRuntime =>
        RecursiveIfCursor cx results depth innerSelected innerSource innerBefore innerBuilt innerInitial innerStart innerMap innerRequired innerRuntime)
      selected source before built initial start map required runtime

theorem GeneratedGenericBlockPrefixDemand.mapCursor {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    {source : BlockSource cfg env [] block state} {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame}
    {cursor next : ∀ {statement : Stmt} {innerState : St}, StmtSource cfg
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } statement innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    {suffix : DemandRuntimePoint → Prop} {runtime : DemandRuntimePoint}
    (convert : ∀ {statement : Stmt} {innerState : St} (source : StmtSource cfg
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } statement innerState)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      cursor source before built initial start map required runtime → next source before built initial start map required runtime)
    (demanded : GeneratedGenericBlockPrefixDemand source selected map required before loop initial cursor suffix runtime) :
    GeneratedGenericBlockPrefixDemand source selected map required before loop initial next suffix runtime := by
  cases demanded with
  | emitted cursor => exact .emitted cursor
  | suffix cursor => exact .suffix cursor
  | body canonical cursor => exact .body canonical (cursor.map convert)

theorem RecursiveIfCursor.succ {cfg : Cfg} {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (depth : Nat) {env : Env}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (demanded : RecursiveIfCursor cx results depth selected source before built initial start map required runtime) :
    RecursiveIfCursor cx results (depth + 1) selected source before built initial start map required runtime := by
  induction depth generalizing env statement state before built initial start map required runtime with
  | zero => exact .base (.scalar demanded)
  | succ depth ih =>
    cases demanded with
    | base cursor => exact .base cursor
    | branch child boolean fuel conditionCanonical evaluated indexEq found branch canonical demanded =>
      apply RecursiveIfCursorStep.branch child boolean fuel conditionCanonical evaluated indexEq found branch canonical
      apply demanded.mapCursor
      intro innerStatement innerState innerSource innerBefore innerBuilt innerInitial innerStart innerMap innerRequired innerRuntime innerDemanded
      exact ih innerDemanded

theorem RecursiveIfCursor.mono {cfg : Cfg} {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {depth larger : Nat} {env : Env}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (demanded : RecursiveIfCursor cx results depth selected source before built initial start map required runtime)
    (bound : depth ≤ larger) : RecursiveIfCursor cx results larger selected source before built initial start map required runtime := by
  induction bound with
  | refl => exact demanded
  | @step larger bound ih => exact RecursiveIfCursor.succ larger ih

def RecursiveIfBranchFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (block : Core.Block) : Prop :=
  ∀ (state : St) (before : LS),
    GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before none [] false block block.stmts
      (@RecursiveIfCursor cfg cx results root owner depth { env with scopes := (block.scope, state.nextScope) :: env.scopes } selected) ∧
    GeneratedStoppedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before none [] false block block.stmts

#print axioms RecursiveIfCursor.mono
#print axioms RecursiveIfCursor.succ
#print axioms GeneratedGenericBlockPrefixDemand.mapCursor
#print axioms RecursiveIfCursor
end Goose.Lower
