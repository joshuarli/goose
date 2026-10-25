import Goose.Lower.DemandGeneratedConstruction
import Goose.Lower.TypedExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

private theorem retained_context_heq {module : Core.Module}
    {firstPlans secondPlans : Array (Array DemandPoint)} {firstPath secondPath : List Nat}
    {node : DemandNode} {phase : DemandPhase}
    {first : EvaluationContext module firstPlans firstPath node phase}
    {second : EvaluationContext module secondPlans secondPath node phase}
    (plans : firstPlans = secondPlans) (path : firstPath = secondPath)
    (same : HEq first second) : first.retained = second.retained := by
  subst secondPlans
  subst secondPath
  exact congrArg EvaluationContext.retained (eq_of_heq same)

theorem RetainedSsaMap.addRuns_realizes {map : RetainedSsaMap}
    {module : Core.Module} {world : World} {env : Env} {runtime : DemandRuntimePoint}
    (realized : map.Realizes module world env runtime) {id : ValueId} {aliases : List RetainedAlias}
    (produced : ∀ alias ∈ aliases, RunAliasAt module world env runtime.state.store runtime.frame id alias) :
    (map.addRuns id aliases).Realizes module world env runtime := by
  constructor
  · exact realized.1
  · intro cell member
    rcases List.mem_append.mp member with added | old
    · obtain ⟨alias, aliasMember, equal⟩ := List.mem_map.mp added
      cases equal
      exact produced alias aliasMember
    · exact realized.2 cell old

theorem RetainedSsaMap.addValues_realizes {map : RetainedSsaMap}
    {module : Core.Module} {world : World} {env : Env} {runtime : DemandRuntimePoint}
    (realized : map.Realizes module world env runtime) {id : ValueId} {aliases : List RetainedAlias}
    (produced : ∀ alias ∈ aliases, ValueAliasAt module world env runtime.state.store runtime.frame id alias) :
    (map.addValues id aliases).Realizes module world env runtime := by
  constructor
  · intro cell member
    rcases List.mem_append.mp member with added | old
    · obtain ⟨alias, aliasMember, equal⟩ := List.mem_map.mp added
      cases equal
      exact produced alias aliasMember
    · exact realized.1 cell old
  · exact realized.2

theorem RetainedSsaMap.Covers.addRuns {map required : RetainedSsaMap}
    (coverage : map.Covers required) (id : ValueId) (aliases : List RetainedAlias) :
    (map.addRuns id aliases).Covers (required.addRuns id aliases) := by
  constructor
  · exact coverage.1
  · intro cell member
    rcases List.mem_append.mp member with added | old
    · exact List.mem_append_left _ added
    · exact List.mem_append_right _ (coverage.2 cell old)

theorem RetainedSsaMap.addRuns_admitted {map : RetainedSsaMap} {profile : ArtifactProfile}
    {retained : List RetainedAlias} (admitted : map.Admitted profile retained)
    {id : ValueId} {aliases : List RetainedAlias}
    (produced : profile = .shrink → ∀ alias ∈ aliases, alias ∈ retained) :
    (map.addRuns id aliases).Admitted profile retained := by
  intro shrink alias member
  change alias ∈ map.values.map Prod.snd ++ (aliases.map (fun alias => (id, alias)) ++ map.runs).map Prod.snd at member
  simp only [List.map_append, List.map_map, Function.comp_def, List.mem_append] at member
  rcases member with old | added | old
  · exact admitted shrink alias (List.mem_append_left _ old)
  · exact produced shrink alias (by simpa using added)
  · exact admitted shrink alias (List.mem_append_right _ old)

theorem RetainedSsaMap.addRuns_bounded {map : RetainedSsaMap} {frontier id : ValueId}
    (bounded : map.Bounded frontier) (fresh : id < frontier) (aliases : List RetainedAlias) :
    (map.addRuns id aliases).Bounded frontier := by
  constructor
  · exact bounded.1
  · intro cell member
    rcases List.mem_append.mp member with added | old
    · obtain ⟨alias, _, equal⟩ := List.mem_map.mp added
      cases equal
      exact fresh
    · exact bounded.2 cell old

theorem ViewResult.generated_runs {cfg : Cfg} {env : Env} {view : View} {state after : St}
    {source : ViewSource cfg env view state} {sample : ViewVal}
    (result : ViewResult source sample after) {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView source.path view = .ok aliases)
    {frame : GIR.Frame} {id : ValueId} (cell : frame.vals[id]? = some (.view sample)) :
    ∀ alias ∈ aliases, RunAliasAt cfg.mod source.world env after.store frame id alias := by
  have modules : source.typingEnv.mod = source.rootsEnv.mod :=
    source.frame.mod_t.trans source.frame.mod_p.symm
  have variables : source.typingEnv.vars = source.rootsEnv.impl.vars :=
    source.frame.vars_t.trans source.frame.vars_p.symm
  have element : source.rootsEnv.access.viewElement? view = some source.element :=
    tyView_accessElement modules variables source.typed
  have aliasQuery := query
  cases rootsAt : source.rootsEnv.access.viewRoots view with
  | error error =>
    simp only [AccessEnv.aliasView, element, rootsAt] at query
    change Except.error error = Except.ok aliases at query
    cases query
  | ok roots =>
    simp only [AccessEnv.aliasView, element, rootsAt] at query
    change Except.ok [⟨.slice .readOnly source.element, roots, .operand source.path⟩] = Except.ok aliases at query
    have aliasesEq := (Except.ok.inj query).symm
    subst aliases
    intro alias member
    have aliasEq : alias = ⟨.slice .readOnly source.element, roots, .operand source.path⟩ := by
      simpa only [List.mem_singleton] using member
    subst alias
    exact Or.inl ⟨sample, .readOnly, source.element, cell, rfl,
      AliasAt.ofAliasView (penv := source.rootsEnv) aliasQuery element source.rooted result.typed result.rooted⟩

theorem ViewResult.extend_generated_runs {cfg : Cfg} {env : Env} {view : View} {state after : St}
    {source : ViewSource cfg env view state} {sample : ViewVal}
    (result : ViewResult source sample after) {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView source.path view = .ok aliases)
    {map : RetainedSsaMap} {frame : GIR.Frame} {id : ValueId} {point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩)
    (cell : frame.vals[id]? = some (.view sample)) :
    (map.addRuns id aliases).Realizes cfg.mod source.world env ⟨point, frame, after⟩ :=
  RetainedSsaMap.addRuns_realizes realized (result.generated_runs query cell)

theorem PlaceSource.ExpressionChildAt.index_retains_generated {cfg : Cfg} {env : Env}
    {view : View} {index : Expr} {origin : OriginId} {state after : St}
    {source : PlaceSource cfg env (.elem view index origin) state}
    {child : ExprSource cfg env index after} (canonical : source.ExpressionChildAt child 1 rfl)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView (source.path ++ [0]) view = .ok aliases)
    (shrink : cfg.mod.profile = .shrink) : ∀ alias ∈ aliases, alias ∈ child.context.retained := by
  have retainedEq := retained_context_heq canonical.plans canonical.path canonical.context
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
    let transition := context.child rfl 1 (.expression index) .expression rfl (by trivial)
    have generated : (DemandNode.place (.elem view index origin)).retainedForChild
        planContext.approvals.access source.path 1 = .ok aliases := by
      simpa [DemandNode.retainedForChild, accessEq] using query
    intro alias member
    have included := DemandNode.childFrame_newAlias transition.childFrameEq generated member
    change alias ∈ transition.context.expected.frame.retained
    rw [transition.expectedFrameEq]
    exact DemandNode.phaseFrame_retains transition.phaseFrameEq included

end Goose.Lower
