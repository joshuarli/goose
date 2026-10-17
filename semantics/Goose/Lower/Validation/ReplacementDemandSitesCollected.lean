import Goose.Lower.Validation.ReplacementSourceSites
import Goose.Lower.Validation.ReplacementDemandSitesContexts

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem ReplacementSitesBuilder.finishBlocks_sourceRoot {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func}
    (checked : ReplacementSitesBuilder (root := root) (targets := targets) le state)
    (blocks : func.blocks = Goose.Lower.finishBlocks state.blocks)
    {blockIndex : Nat} {block : GIR.Block} (row : func.blocks[blockIndex]? = some block)
    {position : Nat} {owner value : ValueId} {origin : Option OriginId}
    (present : block.insts[position]? = some (.eff (.replace owner value origin))) :
    ∃ sourceOrigin, origin = some sourceOrigin ∧
      ∃ site : ReplacementSiteAt le state blockIndex position owner value sourceOrigin,
        site.source.sourceRoot = root := by
  rw [blocks, Goose.Lower.finishBlocks, Array.getElem?_map] at row
  cases bodyRow : state.blocks[blockIndex]? with
  | none => simp [bodyRow] at row
  | some body =>
    simp only [bodyRow, Option.map_some, Option.some.injEq] at row
    subst block
    have authority := checked blockIndex body bodyRow position (.eff (.replace owner value origin))
      (by simpa using present)
    cases origin with
    | none => exact False.elim authority
    | some sourceOrigin =>
      obtain ⟨witness⟩ := authority
      exact ⟨sourceOrigin, rfl, witness.site, witness.root_eq⟩

theorem replacementDemandContext_forContext {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {contextIndex : ContextId} {context : Context}
    (contextAt : module.contexts[contextIndex]? = some context) {impl : Core.Impl}
    (implAt : module.impls[context.impl]? = some impl) {results : List Ty} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite (lowerEnv module impl.vars results) state owner value origin)
    (rootEq : site.sourceRoot = .block impl.body) :
    Nonempty (ReplacementDemandContext module contextIndex site.sourcePath site.place site.rhs origin) := by
  have moduleEq : site.sourceEnv.mod = module := congrArg LEnv.mod site.environment
  have shrink : module.profile = .shrink := by
    simpa only [moduleEq] using tyStmt_assignWhole_profile site.accepted
  obtain ⟨plans, derived, wellFormed⟩ := (validate_modOk module accepted).demandPlans
  let selection := PlanContext.forContext derived wellFormed (by rw [shrink]; decide) contextAt impl implAt
  let location : ReplacementDemandLocation (.block impl.body) (.statement (.assignWhole site.place site.rhs origin)) :=
    ⟨site.sourcePath, by rw [← rootEq]; exact site.structuralSource⟩
  have rootAt : demandRoot? module selection.planContext.owner = some (.block impl.body) := by
    rw [selection.ownerEq]
    have selected := selection.rootAt
    rw [selection.rootNode] at selected
    exact selected
  exact ⟨⟨plans, selection.planContext, selection.ownerEq, shrink,
    location.context selection.planContext rootAt⟩⟩

theorem replacementDemandContext_forGlobal {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {globalIndex : GlobalId} {global : Core.Global}
    (globalAt : module.globals[globalIndex]? = some global) {results : List Ty} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite (lowerEnv module #[] results) state owner value origin)
    (rootEq : site.sourceRoot = .expression global.init) :
    Nonempty (ReplacementDemandContext module (module.contexts.size + globalIndex)
      site.sourcePath site.place site.rhs origin) := by
  have moduleEq : site.sourceEnv.mod = module := congrArg LEnv.mod site.environment
  have shrink : module.profile = .shrink := by
    simpa only [moduleEq] using tyStmt_assignWhole_profile site.accepted
  obtain ⟨plans, derived, wellFormed⟩ := (validate_modOk module accepted).demandPlans
  let selection := PlanContext.forGlobal derived wellFormed (by rw [shrink]; decide) globalAt
  let location : ReplacementDemandLocation (.expression global.init) (.statement (.assignWhole site.place site.rhs origin)) :=
    ⟨site.sourcePath, by rw [← rootEq]; exact site.structuralSource⟩
  have rootAt : demandRoot? module selection.planContext.owner = some (.expression global.init) := by
    rw [selection.ownerEq]
    have selected := selection.rootAt
    rw [selection.rootNode] at selected
    exact selected
  exact ⟨⟨plans, selection.planContext, selection.ownerEq, shrink,
    location.context selection.planContext rootAt⟩⟩

end Goose.Lower.Validation
