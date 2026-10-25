import Goose.Lower.Validation.ReplacementDemandSitesContexts

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

theorem ReplacementDemandContext.owner_forbidden {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin) :
    ∃ target, context.planContext.approvals.access.owner place = .ok target ∧
      target ∈ context.rhsContext.forbiddenOwners := by
  let mutation := context.statement.phase rfl .mutation
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  obtain ⟨target, lookup, _⟩ := mutation.context.sourceAt.directShrinkOwner_result (place := place) rfl
    (by simp [DemandNode.directShrinkPlace?]) context.planContext.approvals.accessMatches
  exact ⟨target, lookup, context.rhs_owner_forbidden lookup⟩

theorem ReplacementDemandContext.accessAt {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin) :
    demandAccess? module owner = some context.planContext.approvals.access := by
  simpa only [context.owner_eq] using context.planContext.approvals.accessMatches

theorem ReplacementDemandContext.access_context {module : Core.Module}
    {contextIndex : ContextId} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module contextIndex path place rhs origin)
    {sourceContext : Context} (contextAt : module.contexts[contextIndex]? = some sourceContext)
    {impl : Impl} (implAt : module.impls[sourceContext.impl]? = some impl) :
    context.planContext.approvals.access = (⟨module, impl, sourceContext⟩ : AccessEnv) :=
  Option.some.inj (context.accessAt.symm.trans (demandAccess?_context contextAt implAt))

theorem ReplacementDemandContext.owner_bound {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin) :
    owner < module.contexts.size + module.globals.size := by
  have bound := (Array.getElem?_eq_some_iff.mp context.planContext.ownerPlan).1
  have size : context.plans.size = module.contexts.size + module.globals.size := by
    simpa [context.shrink] using context.planContext.wellFormed.1
  simpa only [size, context.owner_eq] using bound

theorem ReplacementDemandContext.access_global {module : Core.Module}
    {globalIndex : GlobalId} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module (module.contexts.size + globalIndex) path place rhs origin) :
    context.planContext.approvals.access = (⟨module, initImpl, initContext⟩ : AccessEnv) := by
  rcases demandAccess?_cases context.accessAt with
    ⟨selectedContext, impl, earlier, contextAt, implAt, access⟩ |
    ⟨global, later, globalAt, access⟩
  · omega
  · exact access

#print axioms ReplacementDemandContext.owner_forbidden
#print axioms ReplacementDemandContext.access_context

end Goose.Lower.Validation
