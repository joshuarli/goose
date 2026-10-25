import Goose.Lower.DemandExpressionCursor

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem expression_definition_demand_traversal {cfg : Cfg} {env : Env} {expression : Expr}
    {state intermediate after : St} (source : ExprSource cfg env expression state)
    {sourceFuel : Nat} {value : Val}
    (done : evalExpr sourceFuel cfg env expression state = .ok value after)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before middle built : LS} {initial frame : GIR.Frame} {start point : Pt}
    {cells : List (ValueId × RVal)} {id : ValueId} {op : Op} {le : LEnv}
    (post : Post cfg env cx before initial middle frame point cells)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (emitted : emitDef op le middle = (id, built)) (extension : ExtT built cx.fn.blocks)
    (notCall : ∀ context arguments origin, op ≠ .call context arguments origin)
    (operation : execPure cx frame op intermediate = .ok (.val value) after)
    {length fuel : Nat} (room : length < fuel)
    (traversal : DemandTraversal cx (CanonicalExpressionDemand map cx source) length fuel
      ⟨start, initial, state⟩ ⟨point, frame, intermediate⟩) :
    ExpressionDemandBoundary source map cx before initial built id value after
        (point.1, point.2 + 1) (frame.set id (.val value)) ∧
      DemandTraversal cx (CanonicalExpressionDemand map cx source) (length + 1) fuel
        ⟨start, initial, state⟩ ⟨(point.1, point.2 + 1), frame.set id (.val value), after⟩ := by
  obtain ⟨finalPost, instruction⟩ := Post.def_leaf post emitted extension (.val value)
  have boundary := ExpressionDemandBoundary.of_result (source.result _ _ done)
    admitted bounded realized finalPost
  have execution : execOp (fuel - length - 1) cx frame op intermediate = .ok (.val value) after := by
    have pureOp : execOp (fuel - length - 1) cx frame op = execPure cx frame op := by
      cases op with
      | call context arguments origin => exact (notCall context arguments origin rfl).elim
      | _ => unfold execOp; rfl
    rw [pureOp]
    exact operation
  have last : DemandTraversal cx (CanonicalExpressionDemand map cx source) 1 (fuel - length)
      ⟨point, frame, intermediate⟩ ⟨(point.1, point.2 + 1), frame.set id (.val value), after⟩ := by
    have remainder : fuel - length = (fuel - length - 1) + 1 := by omega
    rw [remainder]
    exact .next traversal.last_valid (.definition instruction execution) (.done _ (.exit boundary.demanded))
  exact ⟨boundary, traversal.append last⟩

theorem expression_definition_demand_stopped {cfg : Cfg} {env : Env} {expression : Expr} {state intermediate after : St}
    (source : ExprSource cfg env expression state) {map : RetainedSsaMap} {cx : FnCtx}
    {before middle built : LS} {initial frame : GIR.Frame} {start point : Pt}
    {cells : List (ValueId × RVal)} {id : ValueId} {op : Op} {le : LEnv} {stop : Stop}
    (post : Post cfg env cx before initial middle frame point cells)
    (emitted : emitDef op le middle = (id, built)) (extension : ExtT built cx.fn.blocks)
    (notCall : ∀ context arguments origin, op ≠ .call context arguments origin)
    (operation : execPure cx frame op intermediate = .stop stop after)
    {length fuel : Nat} (room : length < fuel)
    (traversal : DemandTraversal cx (CanonicalExpressionDemand map cx source) length fuel
      ⟨start, initial, state⟩ ⟨point, frame, intermediate⟩) :
    DemandStoppedTraversal cx (CanonicalExpressionDemand map cx source) length fuel
      ⟨start, initial, state⟩ stop after := by
  have instruction := (Post.def_leaf post emitted extension (.val .unit)).2
  have execution : execOp (fuel - length - 1) cx frame op intermediate = .stop stop after := by
    have pureOp : execOp (fuel - length - 1) cx frame op = execPure cx frame op := by
      cases op with
      | call context arguments origin => exact (notCall context arguments origin rfl).elim
      | _ => unfold execOp; rfl
    rw [pureOp]
    exact operation
  refine ⟨⟨point, frame, intermediate⟩, traversal, ?_⟩
  have remainder : fuel - length = (fuel - length - 1) + 1 := by omega
  rw [remainder]
  exact .definition instruction execution

end Goose.Lower
