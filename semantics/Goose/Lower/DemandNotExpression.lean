import Goose.Lower.DemandExpressionSuffix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem not_demand_traversal {cfg : Cfg} {env : Env} {expression : Expr} {state after : St}
    (source : ExprSource cfg env (.not expression) state) (child : ExprSource cfg env expression state)
    (metadata : source.ChildAt child 0 rfl)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before middle built : LS} {initial frame : GIR.Frame} {start point : Pt}
    {argument id : ValueId} {le : LEnv} {sourceFuel : Nat} {value : Bool}
    (done : evalExpr sourceFuel cfg env expression state = .ok (.bool value) after)
    (post : Post cfg env cx before initial middle frame point [(argument, .val (.bool value))])
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (emitted : emitDef (.boolNot argument) le middle = (id, built)) (extension : ExtT built cx.fn.blocks)
    {length fuel : Nat} (room : length < fuel)
    (traversal : DemandTraversal cx (CanonicalExpressionDemand map cx child) length fuel
      ⟨start, initial, state⟩ ⟨point, frame, after⟩) :
    evalExpr (sourceFuel + 1) cfg env (.not expression) state = .ok (.bool (!value)) after ∧
      Post cfg env cx before initial built (frame.set id (.val (.bool (!value))))
        (point.1, point.2 + 1) [(id, .val (.bool (!value)))] ∧
      DemandTraversal cx (CanonicalExpressionDemand map cx source) (length + 1) fuel
        ⟨start, initial, state⟩ ⟨(point.1, point.2 + 1), frame.set id (.val (.bool (!value))), after⟩ := by
  have sourceDone : evalExpr (sourceFuel + 1) cfg env (.not expression) state =
      .ok (.bool (!value)) after := by
    simp only [evalExpr, bind_apply, done, Core.expectBool, pure_apply]
  have first : DemandTraversal cx (CanonicalExpressionDemand map cx source) length fuel
      ⟨start, initial, state⟩ ⟨point, frame, after⟩ :=
    traversal.mono (fun _ demanded => .child metadata demanded)
  have cell := post.has (argument, .val (.bool value)) (by simp)
  have operation : execPure cx frame (.boolNot argument) after =
      .ok (.val (.bool (!value))) after := by
    simp only [execPure, getVal_of cell, pure_bind, Core.expectBool, pure_apply]
  obtain ⟨boundary, result⟩ := expression_definition_demand_traversal source sourceDone admitted post
    bounded realized emitted extension (by intro context arguments origin impossible; cases impossible)
    operation room first
  exact ⟨sourceDone, boundary.post, result⟩


end Goose.Lower
