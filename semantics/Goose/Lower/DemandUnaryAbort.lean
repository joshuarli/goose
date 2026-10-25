import Goose.Lower.DemandUnaryExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem un_demand_abort {cfg : Cfg} {env : Env} {expression : Expr} {state intermediate : St}
    {operation : UnOp} {origin : OriginId} (source : ExprSource cfg env (.un operation expression origin) state)
    (child : ExprSource cfg env expression state) (metadata : source.ChildAt child 0 rfl)
    {map : RetainedSsaMap} {cx : FnCtx} {before middle built : LS} {initial frame : GIR.Frame} {start point : Pt}
    {argument id : ValueId} {le : LEnv} {sourceFuel : Nat} {type : IntTy} {number : Int} {kind : NumAbort}
    (done : evalExpr sourceFuel cfg env expression state = .ok (.int type number) intermediate)
    (computed : evalUn cfg.profile operation type number = .error kind)
    (post : Post cfg env cx before initial middle frame point [(argument, .val (.int type number))])
    (emitted : emitDef (.un operation type argument (some origin)) le middle = (id, built))
    (extension : ExtT built cx.fn.blocks) {length fuel : Nat} (room : length < fuel)
    (traversal : DemandTraversal cx (CanonicalExpressionDemand map cx child) length fuel
      ⟨start, initial, state⟩ ⟨point, frame, intermediate⟩) :
    evalExpr (sourceFuel + 1) cfg env (.un operation expression origin) state =
        .stop (.abort (AbortKind.ofNum kind) origin) intermediate ∧
      DemandStoppedTraversal cx (CanonicalExpressionDemand map cx source) length fuel
        ⟨start, initial, state⟩ (.abort (AbortKind.ofNum kind) origin) intermediate := by
  have sourceDone : evalExpr (sourceFuel + 1) cfg env (.un operation expression origin) state =
      .stop (.abort (AbortKind.ofNum kind) origin) intermediate := by
    simp only [evalExpr, bind_apply, done, Core.expectInt, pure_apply, computed, abortAt, M.stop]
  have cell := post.has (argument, .val (.int type number)) (by simp)
  have execution : execPure cx frame (.un operation type argument (some origin)) intermediate =
      .stop (.abort (AbortKind.ofNum kind) origin) intermediate := by
    rw [execPure_un post.rel.prof cell, computed]
    rfl
  refine ⟨sourceDone, expression_definition_demand_stopped source post emitted extension
    (by intro context arguments origin impossible; cases impossible) execution room ?_⟩
  exact traversal.mono (fun _ demanded => .child metadata demanded)

theorem conv_demand_abort {cfg : Cfg} {env : Env} {expression : Expr} {state intermediate : St}
    {operation : ConvKind} {origin : OriginId} {target : IntTy}
    (source : ExprSource cfg env (.conv operation (.int target) expression origin) state)
    (child : ExprSource cfg env expression state) (metadata : source.ChildAt child 0 rfl)
    {map : RetainedSsaMap} {cx : FnCtx} {before middle built : LS} {initial frame : GIR.Frame} {start point : Pt}
    {argument id : ValueId} {le : LEnv} {sourceFuel : Nat} {type : IntTy} {number : Int} {kind : NumAbort}
    (done : evalExpr sourceFuel cfg env expression state = .ok (.int type number) intermediate)
    (computed : evalConv cfg.profile operation type target number = .error kind)
    (post : Post cfg env cx before initial middle frame point [(argument, .val (.int type number))])
    (emitted : emitDef (.conv operation type target argument (some origin)) le middle = (id, built))
    (extension : ExtT built cx.fn.blocks) {length fuel : Nat} (room : length < fuel)
    (traversal : DemandTraversal cx (CanonicalExpressionDemand map cx child) length fuel
      ⟨start, initial, state⟩ ⟨point, frame, intermediate⟩) :
    evalExpr (sourceFuel + 1) cfg env (.conv operation (.int target) expression origin) state =
        .stop (.abort (AbortKind.ofNum kind) origin) intermediate ∧
      DemandStoppedTraversal cx (CanonicalExpressionDemand map cx source) length fuel
        ⟨start, initial, state⟩ (.abort (AbortKind.ofNum kind) origin) intermediate := by
  have sourceDone : evalExpr (sourceFuel + 1) cfg env (.conv operation (.int target) expression origin) state =
      .stop (.abort (AbortKind.ofNum kind) origin) intermediate := by
    simp only [evalExpr, bind_apply, done, Core.expectInt, Core.expectIntTy, pure_apply, computed, abortAt, M.stop]
  have cell := post.has (argument, .val (.int type number)) (by simp)
  have execution : execPure cx frame (.conv operation type target argument (some origin)) intermediate =
      .stop (.abort (AbortKind.ofNum kind) origin) intermediate := by
    rw [execPure_conv post.rel.prof cell, computed]
    rfl
  refine ⟨sourceDone, expression_definition_demand_stopped source post emitted extension
    (by intro context arguments origin impossible; cases impossible) execution room ?_⟩
  exact traversal.mono (fun _ demanded => .child metadata demanded)

end Goose.Lower
