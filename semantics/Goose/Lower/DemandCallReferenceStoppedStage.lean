import Goose.Lower.DemandCallReferenceComplete
import Goose.Lower.DemandCallPrefixCompare

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_call_reference_stopped_stage {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {mutability : Mutability} {place : Place}
    (found : arguments[index]? = some (.byRef mutability place)) (child : PlaceSource cfg env place state)
    (target : child.ty.refTarget = true)
    (canonical : (ArgSource.byRef mutability child (Or.inl target)).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef mutability place) found))
    (form : ScalarReadPlace place) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {initial : GIR.Frame} {start : Pt}
    (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) 
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {fuel : Nat} {stop : Stop} {after : St} (stopped : DemandInstructionStop cx fuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ (location : Loc) (consumed remaining : Nat) (point : Pt) (frame : GIR.Frame) (aliases : List RetainedAlias),
      let stage := (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2
      let id := (lowerArg (.byRef mutability place) (lowerEnv cfg.mod env.vars results) stage).1
      let nextPrior := prior ++ aliases.map (fun alias => (id, alias))
      consumed + remaining = taken ∧
      DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      DemandRuntimePrefix cx remaining ⟨point, frame, state⟩ reached ∧
      evalArg 2 cfg env (.byRef mutability place) state = .ok (.ref location) state ∧
      Post cfg env cx stage initial (lowerArg (.byRef mutability place) (lowerEnv cfg.mod env.vars results) stage).2
        frame point [(id, .val (.ref location))] ∧
      GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1 nextPrior ∧
      (⟨nextPrior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (⟨nextPrior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  obtain ⟨location, length, point, frame, aliases, evaluated, first, tail, finalPost, nextTracked, nextRealized, nextBounded, nextInput⟩ :=
    accepted_generated_call_reference_complete source found child target canonical form occurrence rows tracked bounded realized input extended
  have executed := DemandRuntimePrefix.next ((first 0).runtime) tail
  obtain ⟨remaining, count, residual⟩ := executed.compare_stopped steps stopped nonTimeout
  exact ⟨location, length + 1, remaining, point, frame, aliases, count, executed, residual,
    evaluated, finalPost, nextTracked, nextRealized, nextBounded, nextInput⟩

#print axioms accepted_generated_call_reference_stopped_stage
end Goose.Lower
