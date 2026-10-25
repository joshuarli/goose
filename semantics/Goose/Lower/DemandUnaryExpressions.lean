import Goose.Lower.DemandExpressionSuffix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem un_demand_traversal {cfg : Cfg} {env : Env} {expression : Expr} {state intermediate : St}
    {operation : UnOp} {origin : OriginId} (source : ExprSource cfg env (.un operation expression origin) state)
    (child : ExprSource cfg env expression state) (metadata : source.ChildAt child 0 rfl)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before middle built : LS} {initial frame : GIR.Frame} {start point : Pt}
    {argument id : ValueId} {le : LEnv} {sourceFuel : Nat} {type : IntTy} {number result : Int}
    (done : evalExpr sourceFuel cfg env expression state = .ok (.int type number) intermediate)
    (computed : evalUn cfg.profile operation type number = .ok result)
    (post : Post cfg env cx before initial middle frame point [(argument, .val (.int type number))])
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (emitted : emitDef (.un operation type argument (some origin)) le middle = (id, built))
    (extension : ExtT built cx.fn.blocks) {length fuel : Nat} (room : length < fuel)
    (traversal : DemandTraversal cx (CanonicalExpressionDemand map cx child) length fuel
      ⟨start, initial, state⟩ ⟨point, frame, intermediate⟩) :
    evalExpr (sourceFuel + 1) cfg env (.un operation expression origin) state = .ok (.int type result) intermediate ∧
      ExpressionDemandBoundary source map cx before initial built id (.int type result) intermediate
        (point.1, point.2 + 1) (frame.set id (.val (.int type result))) ∧
      DemandTraversal cx (CanonicalExpressionDemand map cx source) (length + 1) fuel
        ⟨start, initial, state⟩ ⟨(point.1, point.2 + 1), frame.set id (.val (.int type result)), intermediate⟩ := by
  have sourceDone : evalExpr (sourceFuel + 1) cfg env (.un operation expression origin) state =
      .ok (.int type result) intermediate := by
    simp only [evalExpr, bind_apply, done, Core.expectInt, pure_apply, computed]
  have cell := post.has (argument, .val (.int type number)) (by simp)
  have execution : execPure cx frame (.un operation type argument (some origin)) intermediate =
      .ok (.val (.int type result)) intermediate := by
    rw [execPure_un post.rel.prof cell, computed]
    rfl
  obtain ⟨boundary, steps⟩ := expression_definition_demand_traversal source sourceDone admitted post bounded realized
    emitted extension (by intro context arguments origin impossible; cases impossible) execution room
    (traversal.mono (fun _ demanded => .child metadata demanded))
  exact ⟨sourceDone, boundary, steps⟩

theorem conv_demand_traversal {cfg : Cfg} {env : Env} {expression : Expr} {state intermediate : St}
    {kind : ConvKind} {origin : OriginId} {target : IntTy}
    (source : ExprSource cfg env (.conv kind (.int target) expression origin) state)
    (child : ExprSource cfg env expression state) (metadata : source.ChildAt child 0 rfl)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before middle built : LS} {initial frame : GIR.Frame} {start point : Pt}
    {argument id : ValueId} {le : LEnv} {sourceFuel : Nat} {type : IntTy} {number result : Int}
    (done : evalExpr sourceFuel cfg env expression state = .ok (.int type number) intermediate)
    (computed : evalConv cfg.profile kind type target number = .ok result)
    (post : Post cfg env cx before initial middle frame point [(argument, .val (.int type number))])
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (emitted : emitDef (.conv kind type target argument (some origin)) le middle = (id, built))
    (extension : ExtT built cx.fn.blocks) {length fuel : Nat} (room : length < fuel)
    (traversal : DemandTraversal cx (CanonicalExpressionDemand map cx child) length fuel
      ⟨start, initial, state⟩ ⟨point, frame, intermediate⟩) :
    evalExpr (sourceFuel + 1) cfg env (.conv kind (.int target) expression origin) state =
        .ok (.int target result) intermediate ∧
      ExpressionDemandBoundary source map cx before initial built id (.int target result) intermediate
        (point.1, point.2 + 1) (frame.set id (.val (.int target result))) ∧
      DemandTraversal cx (CanonicalExpressionDemand map cx source) (length + 1) fuel
        ⟨start, initial, state⟩ ⟨(point.1, point.2 + 1), frame.set id (.val (.int target result)), intermediate⟩ := by
  have sourceDone : evalExpr (sourceFuel + 1) cfg env (.conv kind (.int target) expression origin) state =
      .ok (.int target result) intermediate := by
    simp only [evalExpr, bind_apply, done, Core.expectInt, Core.expectIntTy, pure_apply, computed]
  have cell := post.has (argument, .val (.int type number)) (by simp)
  have execution : execPure cx frame (.conv kind type target argument (some origin)) intermediate =
      .ok (.val (.int target result)) intermediate := by
    rw [execPure_conv post.rel.prof cell, computed]
    rfl
  obtain ⟨boundary, steps⟩ := expression_definition_demand_traversal source sourceDone admitted post bounded realized
    emitted extension (by intro context arguments origin impossible; cases impossible) execution room
    (traversal.mono (fun _ demanded => .child metadata demanded))
  exact ⟨sourceDone, boundary, steps⟩

theorem fill_demand_traversal {cfg : Cfg} {env : Env} {expression : Expr} {state intermediate : St}
    {element : Ty} {count : Nat} (source : ExprSource cfg env (.fill (.arr element count) expression) state)
    (child : ExprSource cfg env expression state) (metadata : source.ChildAt child 0 rfl)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before middle built : LS} {initial frame : GIR.Frame} {start point : Pt}
    {argument id : ValueId} {le : LEnv} {sourceFuel : Nat} {value : Val}
    (done : evalExpr sourceFuel cfg env expression state = .ok value intermediate)
    (post : Post cfg env cx before initial middle frame point [(argument, .val value)])
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (emitted : emitDef (.arrFill (.arr element count) argument) le middle = (id, built))
    (extension : ExtT built cx.fn.blocks) {length fuel : Nat} (room : length < fuel)
    (traversal : DemandTraversal cx (CanonicalExpressionDemand map cx child) length fuel
      ⟨start, initial, state⟩ ⟨point, frame, intermediate⟩) :
    evalExpr (sourceFuel + 1) cfg env (.fill (.arr element count) expression) state =
        .ok (.fixed (Array.replicate count value)) intermediate ∧
      ExpressionDemandBoundary source map cx before initial built id (.fixed (Array.replicate count value)) intermediate
        (point.1, point.2 + 1) (frame.set id (.val (.fixed (Array.replicate count value)))) ∧
      DemandTraversal cx (CanonicalExpressionDemand map cx source) (length + 1) fuel
        ⟨start, initial, state⟩
        ⟨(point.1, point.2 + 1), frame.set id (.val (.fixed (Array.replicate count value))), intermediate⟩ := by
  have sourceDone : evalExpr (sourceFuel + 1) cfg env (.fill (.arr element count) expression) state =
      .ok (.fixed (Array.replicate count value)) intermediate := by
    simp only [evalExpr, Core.expectFixedCount, bind_apply, done, pure_apply]
  have cell := post.has (argument, .val value) (by simp)
  have execution : execPure cx frame (.arrFill (.arr element count) argument) intermediate =
      .ok (.val (.fixed (Array.replicate count value))) intermediate := by
    simp only [execPure, Core.expectFixedCount, pure_bind, getVal_of cell, pure_apply]
  obtain ⟨boundary, steps⟩ := expression_definition_demand_traversal source sourceDone admitted post bounded realized
    emitted extension (by intro context arguments origin impossible; cases impossible) execution room
    (traversal.mono (fun _ demanded => .child metadata demanded))
  exact ⟨sourceDone, boundary, steps⟩

end Goose.Lower
