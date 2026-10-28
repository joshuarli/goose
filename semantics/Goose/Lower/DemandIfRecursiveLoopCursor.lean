import Goose.Lower.DemandIfRecursiveCursor
import Goose.Lower.DemandControlProgressCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive RecursiveLoopIfCursorStep {cfg : Cfg} (cx : FnCtx) (results : List Ty) {root : DemandNode} {owner : Nat}
    (loop : Option LoopCtx)
    (inner : ∀ {env : Env}, GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner →
      ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
        LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) :
    ∀ {env : Env} (_selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner),
    ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | scalar {env : Env} {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
      {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime) :
      RecursiveLoopIfCursorStep cx results loop inner selected source before built initial start map required runtime
  | condition {env : Env} {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
      {condition : Expr} {yes : Core.Block} {no : Option Core.Block} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.ifS condition yes no origin) state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env condition state)
      (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
      (demanded : CanonicalExpressionDemand map cx child runtime)
      (progress : (∃ id op, instAt cx.fn runtime.point = some (.def id op)) ∨
        ∃ next, ∀ fuel, DemandInstructionStep cx fuel runtime next) :
      RecursiveLoopIfCursorStep cx results loop inner selected source before built initial start map required runtime
  | fork {env : Env} {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
      {condition : Expr} {yes : Core.Block} {no : Option Core.Block} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.ifS condition yes no origin) state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env condition state) (boolean : Bool) (fuel : Nat)
      (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
      (evaluated : evalExpr fuel cfg env condition state = .ok (.bool boolean) runtime.state)
      (boundary : GeneratedExpressionPrefixEnd child map cx before initial
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool boolean) runtime)
      (step : ∃ next, ∀ fuel, DemandInstructionStep cx fuel runtime next) :
      RecursiveLoopIfCursorStep cx results loop inner selected source before built initial start map required runtime
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
      (demanded : GeneratedGenericBlockPrefixDemand branch selected map required branchStart loop branchFrame
        (@inner { env with scopes := (block.scope, middle.nextScope) :: env.scopes } selected)
        (GeneratedBranchBlockEffectDemand branch map required cx results branchStart loop branchFrame) runtime) :
      RecursiveLoopIfCursorStep cx results loop inner selected source before built initial start map required runtime
  | join {env : Env} {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
      {condition : Expr} {yes : Core.Block} {no : Option Core.Block} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.ifS condition yes no origin) state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (joinBlock : BlockId) (fuel : Nat)
      (evaluated : execStmt fuel cfg env (.ifS condition yes no origin) state = .ok (.normal .unit) runtime.state)
      (step : ∀ targetFuel, DemandInstructionStep cx targetFuel runtime ⟨(joinBlock, 0), runtime.frame, runtime.state⟩)
      (post : GeneratedStatementPrefixEnd source map cx before initial built loop (.normal .unit)
        ⟨(joinBlock, 0), runtime.frame, runtime.state⟩) :
      RecursiveLoopIfCursorStep cx results loop inner selected source before built initial start map required runtime

def RecursiveLoopIfCursor {cfg : Cfg} (cx : FnCtx) (results : List Ty) {root : DemandNode} {owner : Nat}
    (loop : Option LoopCtx) (depth : Nat) {env : Env}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
    (before built : LS) (initial : GIR.Frame) (start : Pt) (map required : RetainedSsaMap) (runtime : DemandRuntimePoint) : Prop :=
  match depth with
  | 0 => ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime
  | depth + 1 => RecursiveLoopIfCursorStep cx results loop
      (fun {_innerEnv} innerSelected {_innerStatement} {_innerState} innerSource innerBefore innerBuilt innerInitial innerStart innerMap innerRequired innerRuntime =>
        RecursiveLoopIfCursor cx results loop depth innerSelected innerSource innerBefore innerBuilt innerInitial innerStart innerMap innerRequired innerRuntime)
      selected source before built initial start map required runtime

theorem RecursiveLoopIfCursor.succ {cfg : Cfg} {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (loop : Option LoopCtx) (depth : Nat) {env : Env}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (demanded : RecursiveLoopIfCursor cx results loop depth selected source before built initial start map required runtime) :
    RecursiveLoopIfCursor cx results loop (depth + 1) selected source before built initial start map required runtime := by
  induction depth generalizing env statement state before built initial start map required runtime with
  | zero => exact .scalar demanded
  | succ depth ih =>
    cases demanded with
    | scalar cursor => exact .scalar cursor
    | condition child canonical demanded progress => exact .condition child canonical demanded progress
    | fork child boolean fuel canonical evaluated boundary step => exact .fork child boolean fuel canonical evaluated boundary step
    | join joinBlock fuel evaluated step post => exact .join joinBlock fuel evaluated step post
    | branch child boolean fuel conditionCanonical evaluated indexEq found branch canonical demanded =>
      apply RecursiveLoopIfCursorStep.branch child boolean fuel conditionCanonical evaluated indexEq found branch canonical
      apply demanded.mapCursor
      intro innerStatement innerState innerSource innerBefore innerBuilt innerInitial innerStart innerMap innerRequired innerRuntime innerDemanded
      exact ih innerDemanded

theorem RecursiveLoopIfCursor.mono {cfg : Cfg} {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {loop : Option LoopCtx} {depth larger : Nat} {env : Env}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (demanded : RecursiveLoopIfCursor cx results loop depth selected source before built initial start map required runtime)
    (bound : depth ≤ larger) : RecursiveLoopIfCursor cx results loop larger selected source before built initial start map required runtime := by
  induction bound with
  | refl => exact demanded
  | @step larger bound ih => exact RecursiveLoopIfCursor.succ loop larger ih

def RecursiveLoopIfBranchFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (depth : Nat) (block : Core.Block) : Prop :=
  ∀ (state : St) (before : LS),
    GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] false block block.stmts
      (@RecursiveLoopIfCursor cfg cx results root owner loop depth { env with scopes := (block.scope, state.nextScope) :: env.scopes } selected) ∧
    GeneratedStoppedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] false block block.stmts

#print axioms RecursiveLoopIfCursor.succ
#print axioms RecursiveLoopIfCursor.mono
end Goose.Lower
