import Goose.Lower.DemandBooleanNext
import Goose.Lower.DemandGeneratedExpressionPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

structure GeneratedUniformExpressionCursor {cfg : Cfg} {env : Env} (cx : FnCtx)
    {expression : Expr} {state : St} (source : ExprSource cfg env expression state)
    (_before _built : LS) (_initial : GIR.Frame) (_start : Pt) (map _required : RetainedSsaMap)
    (runtime : DemandRuntimePoint) : Prop where
  demanded : CanonicalExpressionDemand map cx source runtime
  next : ∃ target, ∀ fuel, DemandInstructionStep cx fuel runtime target

theorem accepted_generated_boolean_uniform_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {expression : Expr} (fragment : BooleanNotExpression expression) :
    GeneratedExpressionPrefixFamily cx results selected loop expression (@GeneratedUniformExpressionCursor cfg env cx) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  refine ⟨owned, coverage, ?_⟩
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨sourceFuel, value, finalPoint, finalFrame, evaluated, post, traversal⟩ :=
    accepted_boolean_expression_demand_traversal fragment source admitted bounded realized
      (show lowerExpr expression le before = ((lowerExpr expression le before).1, (lowerExpr expression le before).2) from rfl)
      input.atPoint extended input.related
  by_cases unfinished : taken < fragment.instructions
  · exact .interior ⟨traversal.runtimePrefix_invariant (by omega) steps, traversal.runtimePrefix_next unfinished steps⟩
  · obtain ⟨remaining, count, traversed, residual⟩ := traversal.runtimePrefix_split (by omega) steps
    have boundary := ExpressionDemandBoundary.of_result (source.result sourceFuel (.bool value) evaluated)
      admitted bounded realized post
    exact .complete (by omega) traversed residual evaluated boundary

#print axioms accepted_generated_boolean_uniform_prefix_family
end Goose.Lower
