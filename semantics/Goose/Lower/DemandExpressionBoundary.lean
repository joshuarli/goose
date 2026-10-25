import Goose.Lower.DemandExpressionResult
import Goose.Lower.ReflectionInduction

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_expression_demand_reflection {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    (source : ExprSource cfg env expression state)
    {results : List Ty} (metadata : SourceResults source.typingEnv source.rootsEnv results)
    {before built : LS} {id : ValueId} {point : Pt} {cx : FnCtx} {frame : GIR.Frame}
    (map : RetainedSsaMap) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (lowered : lowerExpr expression (lowerEnv cfg.mod env.vars results) before = (id, built))
    (atPoint : before.pp = some point) (extension : ExtT built cx.fn.blocks)
    (related : Rel cfg env cx frame before) (moduleEq : cx.cfg.mod = lower cfg.mod)
    (resultsEq : cx.fn.results = results) (generated : GeneratedBuilderState before) (fuel : Nat) :
    ReflectAtFuel fuel cx point frame (fun sourceFuel => evalExpr sourceFuel cfg env expression)
      (ExpressionDemandBoundary source map cx before frame built id) state := by
  have reflection := typedExpr_reflection fuel cfg results expression env state source metadata
    before built id point cx frame lowered atPoint extension related moduleEq resultsEq generated
  apply reflection.mono_success
  intro sourceFuel value after finalPoint finalFrame done post
  exact ExpressionDemandBoundary.of_result (source.result sourceFuel value done) admitted bounded realized post

end Goose.Lower
