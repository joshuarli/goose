import Goose.Lower.DemandGeneratedGlobalClearPrefix
import Goose.Lower.DemandScalarPlaceAddress
import Goose.Lower.DemandClearStoppedFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive ScalarClearCursor {cfg : Cfg} {env : Env} {place : Place} {origin : OriginId} {state : St}
    (source : StmtSource cfg env (.clear place origin) state) (map : RetainedSsaMap) (cx : FnCtx) : DemandRuntimePoint → Prop
  | atFrame {runtime : DemandRuntimePoint} {typing : TEnv} {roots : PEnv} {future : _}
      (frame : DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime)
      (progress : (∃ effect, instAt cx.fn runtime.point = some (.eff effect)) ∨
        ∃ next, ∀ fuel, DemandInstructionStep cx fuel runtime next) :
      ScalarClearCursor source map cx runtime

theorem accepted_generated_scalar_clear_prefix {cfg : Cfg} {env : Env} {place : Place} {origin : OriginId} {state : St}
    (source : StmtSource cfg env (.clear place origin) state) (form : ScalarReadPlace place)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.clear place origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {frame : GIR.Frame} {point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (atPoint : before.pp = some point) (related : Rel cfg env cx frame before)
    (extended : ExtT (lowerStmt loop (.clear place origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨point, frame, state⟩ reached) :
    GeneratedStatementPrefixDecomposition source selected occurrence rows map frame point
      (ScalarClearCursor source map cx) taken reached := by
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  obtain ⟨child, _, _, rootsEq, _, _, _, _, canonical⟩ := source.clearChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place place) before := by
    rw [canonical.path]
    exact .clearPlace occurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.clearPlace occurrence) required := .clearPlace rows
    simpa only [rootsEq, canonical.path] using inherited
  obtain ⟨location, placed, addressPost, firstStep⟩ := accepted_generated_scalar_place_address child form
    childOccurrence childRows atPoint related (generated_clear_place_extended extended)
  let middle : DemandRuntimePoint := ⟨(point.1, point.2 + 1), frame.set addressed.1 (.val (.ref location)), state⟩
  have placeResult := child.result 1 location placed
  have middleCarried := realized.retained addressPost.same bounded.1 bounded.2 RetainsAliases.refl
  refine ⟨owned, coverage, ?_⟩
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨length, current, rfl, actual, tail⟩
  · exact .interior (.atFrame ⟨⟨_, atPoint, related⟩, source.frame, realized⟩ (Or.inr ⟨middle, firstStep⟩))
  · obtain ⟨actualFuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
    have same := actualStep.deterministic (firstStep actualFuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, boundary, rfl, cleared, residual⟩
    · apply DemandPrefixDecomposition.interior
      apply ScalarClearCursor.atFrame
      have childFrame := placeResult.frame
      rw [canonical.world] at childFrame
      · exact ⟨⟨_, addressPost.pp, addressPost.rel⟩, childFrame, middleCarried⟩
      · have site := GeneratedDemandInstruction.clear_auto occurrence rows addressPost.pp extended
        exact Or.inl ⟨_, site.instruction⟩
    · obtain ⟨_, _, _, _, _, _, _, evaluated, post, result, finalBounded, demanded⟩ :=
        accepted_generated_clear_runtime_step source occurrence rows coverage admitted bounded realized placed addressPost extended cleared
      have prepared : (execStmt 2 cfg env (.clear place origin) >>= prepareLoopFlow env loop) state =
          .ok (.normal .unit) boundary.state := by
        simp only [bind_apply, evaluated]
        cases loop <;> rfl
      exact .complete (by omega) (.next actual (.next cleared (.zero _))) residual prepared
        (.normal post result finalBounded demanded.operands)


inductive ScalarClearPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | clear {place : Place} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.clear place origin) state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
      {runtime : DemandRuntimePoint} (demanded : ScalarClearCursor source map cx runtime) :
      ScalarClearPrefixCursor cx source before built initial start map required runtime

theorem accepted_generated_scalar_clear_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {place : Place} (form : ScalarReadPlace place) (origin : OriginId) :
    GeneratedStatementPrefixFamily cx results selected loop (.clear place origin)
      (@ScalarClearPrefixCursor cfg env cx) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  have progress := accepted_generated_scalar_clear_prefix source form selected owned occurrence rows coverage admitted bounded
    realized input.atPoint input.related extended steps
  refine ⟨owned, coverage, ?_⟩
  cases progress.progress with
  | interior demanded => exact .interior (.clear demanded)
  | complete count prefixSteps residual evaluated post => exact .complete count prefixSteps residual evaluated post

theorem accepted_generated_scalar_clear_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {place : Place} (form : ScalarReadPlace place) (origin : OriginId) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.clear place origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  obtain ⟨child, _, _, rootsEq, _, _, _, _, canonical⟩ := source.clearChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place place) before := by
    rw [canonical.path]
    exact .clearPlace occurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.clearPlace occurrence) required := .clearPlace rows
    simpa only [rootsEq, canonical.path] using inherited
  obtain ⟨location, placed, post, firstStep⟩ := accepted_generated_scalar_place_address child form
    childOccurrence childRows input.atPoint input.related (generated_clear_place_extended extended)
  let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1), initial.set addressed.1 (.val (.ref location)), state⟩
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨length, current, rfl, actual, tail⟩
  · exact (stopped.excludes_step_nonTimeout nonTimeout (firstStep targetFuel)).elim
  · obtain ⟨fuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
    have same := actualStep.deterministic (firstStep fuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, boundary, rfl, cleared, residual⟩
    · have done := accepted_generated_clear_runtime_stop source occurrence rows placed post extended stopped nonTimeout
      refine .aborted 2 ?_
      simp only [bind_apply, done]
    · obtain ⟨_, _, _, _, _, _, _, evaluated, finalPost, result, finalBounded, demanded⟩ :=
        accepted_generated_clear_runtime_step source occurrence rows coverage admitted bounded realized placed post extended cleared
      have prepared : (execStmt 2 cfg env (.clear place origin) >>= prepareLoopFlow env loop) state =
          .ok (.normal .unit) boundary.state := by
        simp only [bind_apply, evaluated]
        cases loop <;> rfl
      exact .complete (by omega) (.next actual (.next cleared (.zero _))) residual prepared
        (.normal finalPost result finalBounded demanded.operands)


#print axioms accepted_generated_scalar_clear_prefix
#print axioms accepted_generated_scalar_clear_prefix_family
#print axioms accepted_generated_scalar_clear_stopped_family

end Goose.Lower
