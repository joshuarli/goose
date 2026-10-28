import Goose.Lower.DemandWhileStoppedFamily
import Goose.Lower.DemandControlProgressCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive WhileHeaderPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | condition {condition : Expr} {body : Core.Block} {origin : OriginId} {state current : St} {count : Nat}
      {source : StmtSource cfg env (.while condition body origin) state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (iterations : WhileIterations cfg env condition body count state current)
      (active : StmtSource cfg env (.while condition body origin) current) (world : active.world = source.world)
      (child : ExprSource cfg env condition current)
      (canonical : active.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
      (demanded : CanonicalExpressionDemand map cx child runtime)
      (progress : (∃ id op, instAt cx.fn runtime.point = some (.def id op)) ∨
        ∃ next, ∀ fuel, DemandInstructionStep cx fuel runtime next) :
      WhileHeaderPrefixCursor cx results selected source before built initial start map required runtime
  | fork {condition : Expr} {body : Core.Block} {origin : OriginId} {state current : St} {count : Nat}
      {source : StmtSource cfg env (.while condition body origin) state} {before built headerState : LS}
      {initial headerFrame : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (iterations : WhileIterations cfg env condition body count state current)
      (active : StmtSource cfg env (.while condition body origin) current) (world : active.world = source.world)
      (child : ExprSource cfg env condition current) (boolean : Bool) (fuel : Nat)
      (canonical : active.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
      (evaluated : evalExpr fuel cfg env condition current = .ok (.bool boolean) runtime.state)
      (boundary : GeneratedExpressionPrefixEnd child map cx headerState headerFrame
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1 (.bool boolean) runtime)
      (step : ∃ next, ∀ fuel, DemandInstructionStep cx fuel runtime next) :
      WhileHeaderPrefixCursor cx results selected source before built initial start map required runtime
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
      (demanded : GeneratedGenericBlockPrefixDemand branch selected map required branchStart
        (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
        conditionFrame
        (@RecursiveLoopIfCursor cfg cx results root owner
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
          (Place._sizeOf_11 body.stmts) { env with scopes := (body.scope, middle.nextScope) :: env.scopes } selected)
        (GeneratedClearBlockDemand branch map required cx results branchStart
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
          conditionFrame) runtime) :
      WhileHeaderPrefixCursor cx results selected source before built initial start map required runtime
  | backEdge {condition : Expr} {body : Core.Block} {origin : OriginId} {state current middle : St} {count : Nat}
      {source : StmtSource cfg env (.while condition body origin) state} {before built branchStart headerState : LS}
      {header exitBlock : BlockId} {initial conditionFrame : GIR.Frame} {start : Pt}
      {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (iterations : WhileIterations cfg env condition body count state current)
      (active : StmtSource cfg env (.while condition body origin) current) (world : active.world = source.world)
      (child : ExprSource cfg env condition current) (conditionFuel bodyFuel : Nat)
      (conditionCanonical : active.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
      (conditionDone : evalExpr conditionFuel cfg env condition current = .ok (.bool true) middle)
      (branch : BlockSource cfg env [] body middle)
      (canonical : active.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]))
      (bodyDone : execBlock bodyFuel cfg env [] body middle = .ok (.normal .unit) runtime.state)
      (ended : GeneratedBranchBlockEnd branch map required cx results branchStart
        (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
        conditionFrame (.normal .unit) runtime)
      (step : ∀ fuel, DemandInstructionStep cx fuel runtime ⟨(header, 0), runtime.frame, runtime.state⟩) :
      WhileHeaderPrefixCursor cx results selected source before built initial start map required runtime

theorem WhileHeaderPrefixCursor.rebase {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial otherInitial : GIR.Frame} {start otherStart : Pt}
    {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : WhileHeaderPrefixCursor cx results selected source before built initial start map required runtime) :
    WhileHeaderPrefixCursor cx results selected source before built otherInitial otherStart map required runtime := by
  cases cursor with
  | condition iterations active world child canonical demanded progress => exact .condition iterations active world child canonical demanded progress
  | fork iterations active world child boolean fuel canonical evaluated boundary step => exact .fork iterations active world child boolean fuel canonical evaluated boundary step
  | body iterations active world child fuel conditionCanonical evaluated branch canonical demanded =>
    exact .body iterations active world child fuel conditionCanonical evaluated branch canonical demanded
  | backEdge iterations active world child conditionFuel bodyFuel conditionCanonical conditionDone branch canonical bodyDone ended step =>
    exact .backEdge iterations active world child conditionFuel bodyFuel conditionCanonical conditionDone branch canonical bodyDone ended step

inductive WhileStatementPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | entry {condition : Expr} {body : Core.Block} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.while condition body origin) state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
      (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
      (step : ∃ next, ∀ fuel, DemandInstructionStep cx fuel ⟨start, initial, state⟩ next) :
      WhileStatementPrefixCursor cx results selected source before built initial start map required ⟨start, initial, state⟩
  | header {statement : Stmt} {state : St} {source : StmtSource cfg env statement state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileHeaderPrefixCursor cx results selected source before built initial start map required runtime) :
      WhileStatementPrefixCursor cx results selected source before built initial start map required runtime

#print axioms WhileHeaderPrefixCursor.rebase
#print axioms WhileStatementPrefixCursor
end Goose.Lower
