import Goose.Lower.DemandGeneratedSliceRuntime

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

private theorem slice_bound_retains_generated {cfg : Cfg} {env : Env} {mutability : Mutability} {view : View}
    {lower upper bound : Bound} {origin : OriginId} {state boundState : St}
    {source : ExprSource cfg env (.slice mutability view lower upper origin) state}
    {child : BoundSource cfg env bound boundState} {index : Nat}
    {found : DemandNode.child? (.expression (.slice mutability view lower upper origin)) index = some (.bound bound)}
    (canonical : source.BoundChildAt child index found) (position : index = 1 ∨ index = 2)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView (source.path ++ [0]) view = .ok aliases)
    (shrink : cfg.mod.profile = .shrink) : ∀ alias ∈ aliases, alias ∈ child.context.retained := by
  have retainedEq := demandContextRetainedEq canonical.plans canonical.path rfl canonical.context
  rw [retainedEq]
  have access := source.access
  cases contextEq : source.context with
  | pilot profile active => exact False.elim (by rw [shrink] at profile; cases profile)
  | @shrink planContext profile context =>
    rw [contextEq] at access
    have accessEq : planContext.approvals.access = source.rootsEnv.access := by
      have moduleEq := access.2.2.1
      have implementationEq := access.2.2.2.1
      have contextEq := access.2.2.2.2
      cases accessAt : planContext.approvals.access
      rw [accessAt] at moduleEq implementationEq contextEq
      unfold PEnv.access
      congr 1
    let transition := context.child rfl index (.bound bound) .bound found (by trivial)
    have generated : (DemandNode.expression (.slice mutability view lower upper origin)).retainedForChild
        planContext.approvals.access source.path index = .ok aliases := by
      rcases position with rfl | rfl <;> simpa [DemandNode.retainedForChild, accessEq] using query
    intro alias member
    have included := DemandNode.childFrame_newAlias transition.childFrameEq generated member
    change alias ∈ transition.context.expected.frame.retained
    rw [transition.expectedFrameEq]
    exact DemandNode.phaseFrame_retains transition.phaseFrameEq included

private theorem view_result_retains {cfg : Cfg} {env : Env} {view : View} {state after : St}
    {source : ViewSource cfg env view state} {sample : ViewVal} {map : RetainedSsaMap}
    (admitted : map.Admitted cfg.mod.profile source.context.retained) (result : ViewResult source sample after) :
    RetainsAliases cfg.mod source.world env state.store after.store (map.values.map Prod.snd ++ map.runs.map Prod.snd) := by
  cases profile : cfg.mod.profile with
  | pilot => exact retainedAliases_of_storeLe (result.pilotStore profile) _
  | shrink => exact result.aliases.subset (admitted profile)

private theorem bound_result_retains {cfg : Cfg} {env : Env} {bound : Bound} {state after : St}
    {source : BoundSource cfg env bound state} {map : RetainedSsaMap}
    (admitted : map.Admitted cfg.mod.profile source.context.retained) (result : BoundResult source after) :
    RetainsAliases cfg.mod source.world env state.store after.store (map.values.map Prod.snd ++ map.runs.map Prod.snd) := by
  cases profile : cfg.mod.profile with
  | pilot => exact retainedAliases_of_storeLe (result.pilotStore profile) _
  | shrink => exact result.aliases.subset (admitted profile)

theorem accepted_generated_slice_operands {cfg : Cfg} {env : Env} {mutability : Mutability} {view : View}
    {lower upper : Bound} {origin : OriginId} {state afterView afterLower afterUpper : St}
    (source : ExprSource cfg env (.slice mutability view lower upper origin) state)
    (operands : SliceOperands lower upper) {fuel : Nat}
    (viewed : evalView (fuel + 1) cfg env view state = .ok operands.sample afterView)
    (lowerEvaluated : operands.lowerOperand.PrefixEvaluated fuel cfg env afterView afterLower)
    (upperEvaluated : operands.upperOperand.PrefixEvaluated fuel cfg env afterLower afterUpper)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root source.path
      (.expression (.slice mutability view lower upper origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {start viewPoint lowerPoint point : Pt}
    {initial viewFrame lowerFrame frame : GIR.Frame}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView (source.path ++ [0]) view = .ok aliases)
    (viewPost : Post cfg env cx before initial (sliceLowerBefore view le before) viewFrame viewPoint
      [((lowerView view le before).1, .view operands.sample)])
    (lowerPost : Post cfg env cx (sliceLowerBefore view le before) viewFrame (sliceUpperBefore view lower le before)
      lowerFrame lowerPoint (operands.lowerOperand.cells le (sliceLowerBefore view le before)))
    (upperPost : Post cfg env cx (sliceUpperBefore view lower le before) lowerFrame
      (sliceEmissionBefore view lower upper le before) frame point
      (operands.upperOperand.cells le (sliceUpperBefore view lower le before))) :
    let requiredRuns := required.addRuns (lowerView view le before).1 aliases
    let carried := map.addRuns (lowerView view le before).1 aliases
    GeneratedDemandRows cfg.mod source.rootsEnv.access (.sliceLower occurrence) requiredRuns ∧
    GeneratedDemandRows cfg.mod source.rootsEnv.access (.sliceUpper occurrence) requiredRuns ∧
    carried.Covers requiredRuns ∧
    ∃ child : BoundSource cfg env upper afterLower, source.BoundChildAt child 2 rfl ∧
      carried.Admitted cfg.mod.profile child.context.retained ∧
      carried.Bounded (sliceEmissionBefore view lower upper le before).vals.size ∧
      Post cfg env cx before initial (sliceEmissionBefore view lower upper le before) frame point
        (operands.cells view le before) ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        carried.values carried.runs ⟨point, frame, afterUpper⟩ := by
  dsimp only
  obtain ⟨sampled, _, viewRoots, viewCanonical, next⟩ := source.sliceChildren mutability origin
  obtain ⟨lowSource, _, _, lowCanonical, nextUpper⟩ := next (fuel + 1) operands.sample afterView viewed
  have lowerDone := operands.lowerOperand.source_evaluated lowerEvaluated (length := operands.sample.len) (default := 0)
  obtain ⟨highSource, _, _, highCanonical⟩ :=
    nextUpper (fuel + 1) (operands.lowerOperand.value operands.sample.len 0) afterLower lowerDone
  have upperDone := operands.upperOperand.source_evaluated upperEvaluated
    (length := operands.sample.len) (default := operands.sample.len)
  have viewResult := sampled.result (fuel + 1) operands.sample viewed
  have lowerResult := lowSource.result (fuel + 1) operands.sample.len 0
    (operands.lowerOperand.value operands.sample.len 0) lowerDone
  have upperResult := highSource.result (fuel + 1) operands.sample.len operands.sample.len
    (operands.upperOperand.value operands.sample.len operands.sample.len) upperDone
  have viewAdmission : map.Admitted cfg.mod.profile sampled.context.retained :=
    fun shrink alias member => viewCanonical.retained alias (admitted shrink alias member)
  have startRealized : map.Realizes cfg.mod sampled.world env ⟨start, initial, state⟩ := by
    simpa only [viewCanonical.world] using realized
  have viewCarried := startRealized.retained viewPost.same bounded.1 bounded.2 (view_result_retains viewAdmission viewResult)
  have viewQuery : sampled.rootsEnv.access.aliasView sampled.path view = .ok aliases := by
    simpa only [viewRoots, viewCanonical.path] using query
  have sampledCell := viewPost.has ((lowerView view le before).1, .view operands.sample) (by simp)
  have augmented := viewResult.extend_generated_runs (point := viewPoint) viewQuery viewCarried sampledCell
  have lowAdmission : (map.addRuns (lowerView view le before).1 aliases).Admitted
      cfg.mod.profile lowSource.context.retained :=
    RetainedSsaMap.addRuns_admitted
      (fun shrink alias member => lowCanonical.retained alias (admitted shrink alias member))
      (slice_bound_retains_generated lowCanonical (Or.inl rfl) query)
  have highAdmission : (map.addRuns (lowerView view le before).1 aliases).Admitted
      cfg.mod.profile highSource.context.retained :=
    RetainedSsaMap.addRuns_admitted
      (fun shrink alias member => highCanonical.retained alias (admitted shrink alias member))
      (slice_bound_retains_generated highCanonical (Or.inr rfl) query)
  have viewBounded := RetainedSsaMap.addRuns_bounded (bounded.mono viewPost.mono)
    (viewPost.lt ((lowerView view le before).1, .view operands.sample) (by simp)) aliases
  have lowStart : (map.addRuns (lowerView view le before).1 aliases).Realizes cfg.mod lowSource.world env
      ⟨viewPoint, viewFrame, afterView⟩ := by
    simpa only [lowCanonical.world, viewCanonical.world, RetainedSsaMap.Realizes] using augmented
  have lowCarried := lowStart.retained lowerPost.same viewBounded.1 viewBounded.2
    (bound_result_retains lowAdmission lowerResult)
  have highStart : (map.addRuns (lowerView view le before).1 aliases).Realizes cfg.mod highSource.world env
      ⟨lowerPoint, lowerFrame, afterLower⟩ := by
    simpa only [highCanonical.world, lowCanonical.world, RetainedSsaMap.Realizes] using lowCarried
  have lowBounded := viewBounded.mono lowerPost.mono
  have highCarried := highStart.retained upperPost.same lowBounded.1 lowBounded.2
    (bound_result_retains highAdmission upperResult)
  refine ⟨.sliceLower rows query, .sliceUpper rows query, coverage.addRuns _ aliases,
    highSource, highCanonical, highAdmission, lowBounded.mono upperPost.mono, ?_,
    ⟨⟨_, upperPost.pp, upperPost.rel⟩, upperResult.frame, highCarried⟩⟩
  simpa only [SliceOperands.cells, List.cons_append, List.nil_append, List.append_assoc] using
    ((viewPost.comp lowerPost).comp upperPost)

end Goose.Lower
