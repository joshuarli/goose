import Goose.Lower.DemandCallReferenceComplete

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_call_reference_demand {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {mutability : Mutability} {place : Place}
    (found : arguments[index]? = some (.byRef mutability place)) (child : PlaceSource cfg env place state)
    (target : child.ty.refTarget = true ∨ (child.ty.isSlice = true ∧ child.mutable = true ∧ place.sliceArg = true))
    (canonical : (ArgSource.byRef mutability child target).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef mutability place) found))
    (form : ScalarReadPlace place) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {frame : GIR.Frame} {point : Pt}
    (atPoint : (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.pp = some point)
    (related : Rel cfg env cx frame (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2)
    (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ location : Loc,
      evalPlace 1 cfg env place state = .ok location state ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
        (prior ++ map.values) map.runs ⟨point, frame, state⟩ ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        (prior ++ map.values) map.runs
        ⟨(point.1, point.2 + 1), frame.set (lowerPlace place (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref location)), state⟩ ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩
        ⟨(point.1, point.2 + 1), frame.set (lowerPlace place (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref location)), state⟩ := by
  obtain ⟨location, placed, post, first⟩ := accepted_generated_call_reference_address source found child target canonical form
    occurrence rows tracked atPoint related extended
  obtain ⟨_, _, world, _, _, _⟩ := canonical
  have carried := realized.retained post.same bounded.1 bounded.2 RetainsAliases.refl
  have initialDemand : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
      (prior ++ map.values) map.runs ⟨point, frame, state⟩ := by
    refine ⟨⟨_, atPoint, related⟩, child.frame, ?_⟩
    simpa only [RetainedSsaMap.Realizes, world] using realized
  have middleDemand : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
      (prior ++ map.values) map.runs
      ⟨(point.1, point.2 + 1), frame.set (lowerPlace place (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref location)), state⟩ := by
    have result := child.result 1 location placed
    refine ⟨⟨_, post.pp, post.rel⟩, result.frame, ?_⟩
    simpa only [world] using carried
  exact ⟨location, placed, initialDemand, middleDemand, first⟩

#print axioms accepted_generated_call_reference_demand
end Goose.Lower
