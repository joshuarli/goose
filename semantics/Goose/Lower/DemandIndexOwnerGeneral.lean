import Goose.Lower.DemandIndexFieldOwner
import Goose.Lower.DemandIndexOwnerForm

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound


inductive GeneratedIndexOwnerSteps (cx : FnCtx) (invariant : DemandRuntimePoint → Prop) (before final : DemandRuntimePoint) : Prop
  | one (step : ∀ fuel, DemandInstructionStep cx fuel before final) : GeneratedIndexOwnerSteps cx invariant before final
  | two (middle : DemandRuntimePoint) (demanded : invariant middle)
      (first : ∀ fuel, DemandInstructionStep cx fuel before middle)
      (second : ∀ fuel, DemandInstructionStep cx fuel middle final) : GeneratedIndexOwnerSteps cx invariant before final

theorem accepted_generated_index_owner_general {cfg : Cfg} {env : Env} {owner : Place} {index : Expr}
    {origin : OriginId} {state : St} (source : PlaceSource cfg env (.elem (.of owner) index origin) state)
    (form : IndexOwnerPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem (.of owner) index origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (atPoint : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerPlace (.elem (.of owner) index origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (fuel : Nat) (location : Loc) (final : DemandRuntimePoint),
      evalPlace fuel cfg env owner state = .ok location state ∧ final.state = state ∧
      Post cfg env cx before initial (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).2 final.frame final.point
        [((lowerPlace owner (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] ∧
      GeneratedIndexOwnerSteps cx (fun runtime => ∃ typing roots future,
        DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime)
        ⟨start, initial, state⟩ final ∧ map.Realizes cfg.mod source.world env final := by
  cases form with
  | scalar scalar =>
    obtain ⟨location, placed, post, step, retained⟩ := accepted_generated_index_owner_address source scalar
      occurrence rows bounded realized atPoint related extended
    exact ⟨1, location, _, placed, rfl, post, .one step, retained⟩
  | field field scalar =>
    obtain ⟨location, middle, final, placed, middleState, finalState, middlePost, first, second, post, retainedMiddle, retainedFinal⟩ :=
      accepted_generated_index_field_owner_address source scalar occurrence rows bounded realized atPoint related extended
    have middleFrame : ∃ typing roots future, DemandFrameAt cfg env cx source.world typing roots future map.values map.runs middle := by
      refine ⟨source.typingEnv, source.rootsEnv, source.context.inputFuture, ⟨⟨_, middlePost.pp, middlePost.rel⟩, ?_, ?_⟩⟩
      · simpa only [middleState] using source.frame
      · simpa only [RetainedSsaMap.Realizes] using retainedMiddle
    exact ⟨2, { location with path := location.path ++ [field] }, final, placed, finalState, post, .two middle middleFrame first second, retainedFinal⟩

inductive GeneratedIndexOwnerProgress (cx : FnCtx) (invariant : DemandRuntimePoint → Prop)
    (before final : DemandRuntimePoint) (taken : Nat) (reached : DemandRuntimePoint) : Prop
  | interior (demanded : invariant reached) : GeneratedIndexOwnerProgress cx invariant before final taken reached
  | arrived {consumed remaining : Nat} (count : consumed + remaining = taken)
      (trace : DemandRuntimePrefix cx consumed before final) (residual : DemandRuntimePrefix cx remaining final reached) :
      GeneratedIndexOwnerProgress cx invariant before final taken reached

theorem GeneratedIndexOwnerSteps.prefix {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {before final : DemandRuntimePoint} (generated : GeneratedIndexOwnerSteps cx invariant before final)
    (initial : invariant before) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken before reached) : GeneratedIndexOwnerProgress cx invariant before final taken reached := by
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨remaining, current, rfl, actual, tail⟩
  · exact .interior initial
  · obtain ⟨fuel, first⟩ := runtimeStep_demandInstructionStep actual
    cases generated with
    | one generated =>
      have same := first.deterministic (generated fuel)
      have currentEq : current = final := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
      subst current
      exact .arrived (by omega) (.next actual (.zero _)) tail
    | two middle demanded generatedFirst generatedSecond =>
      have same := first.deterministic (generatedFirst fuel)
      have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
      subst current
      rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, current, rfl, second, tail⟩
      · exact .interior demanded
      · obtain ⟨fuel, actualSecond⟩ := runtimeStep_demandInstructionStep second
        have same := actualSecond.deterministic (generatedSecond fuel)
        have currentEq : current = final := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
        subst current
        exact .arrived (by omega) (.next actual (.next second (.zero _))) tail

theorem GeneratedIndexOwnerSteps.stopped_prefix {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {before final : DemandRuntimePoint} (generated : GeneratedIndexOwnerSteps cx invariant before final)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken before reached)
    {fuel : Nat} {stop : Stop} {after : St} (stopped : DemandInstructionStop cx fuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ consumed remaining, consumed + remaining = taken ∧ DemandRuntimePrefix cx consumed before final ∧
      DemandRuntimePrefix cx remaining final reached := by
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨remaining, current, rfl, actual, tail⟩
  · cases generated with
    | one step => exact (stopped.excludes_step_nonTimeout nonTimeout (step fuel)).elim
    | two middle demanded first second => exact (stopped.excludes_step_nonTimeout nonTimeout (first fuel)).elim
  · obtain ⟨actualFuel, first⟩ := runtimeStep_demandInstructionStep actual
    cases generated with
    | one step =>
      have same := first.deterministic (step actualFuel)
      have currentEq : current = final := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
      subst current
      exact ⟨1, remaining, by omega, .next actual (.zero _), tail⟩
    | two middle demanded firstStep secondStep =>
      have same := first.deterministic (firstStep actualFuel)
      have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
      subst current
      rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, current, rfl, second, tail⟩
      · exact (stopped.excludes_step_nonTimeout nonTimeout (secondStep fuel)).elim
      · obtain ⟨actualFuel, actualSecond⟩ := runtimeStep_demandInstructionStep second
        have same := actualSecond.deterministic (secondStep actualFuel)
        have currentEq : current = final := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
        subst current
        exact ⟨2, remaining, by omega, .next actual (.next second (.zero _)), tail⟩

#print axioms GeneratedIndexOwnerSteps.stopped_prefix
#print axioms GeneratedIndexOwnerSteps.prefix
#print axioms IndexOwnerPlace.indexed
#print axioms PlaceSource.index_owner_view_alias
#print axioms accepted_generated_index_owner_general
end Goose.Lower
