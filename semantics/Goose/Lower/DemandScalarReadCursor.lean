import Goose.Lower.DemandScalarReadNext

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

structure GeneratedDefinitionExpressionCursor {cfg : Cfg} {env : Env} (cx : FnCtx)
    {expression : Expr} {state : St} (source : ExprSource cfg env expression state)
    (before _built : LS) (initial : GIR.Frame) (_start : Pt) (map required : RetainedSsaMap)
    (runtime : DemandRuntimePoint) : Prop where
  demanded : CanonicalExpressionDemand map cx source runtime
  same : Same before.vals.size initial runtime.frame
  instruction : ∃ label id op, GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required label runtime.point (.def id op)

theorem accepted_generated_read_definition_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {place : Place} (form : ScalarReadPlace place) :
    GeneratedExpressionPrefixFamily cx results selected loop (.read place)
      (@GeneratedDefinitionExpressionCursor cfg env cx) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  obtain ⟨child, typing, roots, metadata⟩ := source.readChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place place) before := by
    rw [metadata.path]
    exact .first occurrence (.expressionPlace rfl)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.first occurrence (.expressionPlace rfl)) required := .first (first := .expressionPlace rfl) rows
    simpa only [roots, metadata.path] using inherited
  obtain ⟨location, placed, post, firstStep⟩ := accepted_generated_scalar_place_address child form
    childOccurrence childRows input.atPoint input.related (generated_read_place_extended extended)
  let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1), initial.set addressed.1 (.val (.ref location)), state⟩
  have carried := realized.retained post.same bounded.1 bounded.2 RetainsAliases.refl
  have atMiddle : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
      map.values map.runs middle := by
    have result := child.result 1 location placed
    have frame := result.frame
    rw [metadata.world, typing, roots, metadata.outputFuture] at frame
    exact ⟨⟨_, post.pp, post.rel⟩, frame, carried⟩
  refine ⟨owned, coverage, ?_⟩
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨length, current, rfl, actual, tail⟩
  · refine .interior ⟨.entry ⟨⟨_, input.atPoint, input.related⟩, source.frame, realized⟩, Same.refl _ _, ?_⟩
    exact accepted_generated_scalar_read_next source form occurrence rows input.atPoint input.related extended (by omega) (.zero _)
  · obtain ⟨fuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
    have same := actualStep.deterministic (firstStep fuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, boundary, rfl, loaded, residual⟩
    · refine .interior ⟨.exit atMiddle, post.same, ?_⟩
      exact accepted_generated_scalar_read_next source form occurrence rows input.atPoint input.related extended (by omega)
        (.next actual (.zero _))
    · obtain ⟨_, _, _, _, value, _, _, evaluated, finalPost, _, _⟩ :=
        accepted_generated_load_runtime_step source occurrence rows coverage placed post (bounded.mono post.mono) carried extended loaded
      have result := source.result 2 value evaluated
      have final := ExpressionDemandBoundary.of_result result admitted bounded realized finalPost
      exact .complete (by omega) (.next actual (.next loaded (.zero _))) residual evaluated final

#print axioms accepted_generated_read_definition_prefix_family
end Goose.Lower
