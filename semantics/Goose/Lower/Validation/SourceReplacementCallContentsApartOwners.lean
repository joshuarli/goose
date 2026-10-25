import Goose.Lower.Validation.SourceReplacementCallContentsApartVisibility
import Goose.Core.Sound.AccessTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Core.Sound ReplacementContentFlowSource

theorem AcceptedReplacementSite.owner_invalidates {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le state owner value origin)
    {access : AccessEnv} {target : DemandOwner}
    (moduleEq : access.mod = site.sourceEnv.mod)
    (variablesEq : access.impl.vars = site.sourceEnv.vars)
    (targetAt : access.owner site.place = .ok target) : target.invalidates = true := by
  obtain ⟨info, element, childStart, source, shape, _, _, _, _⟩ :=
    tyStmt_assignWhole_children site.accepted
  let env : PEnv := ⟨access.mod, access.impl, access.ctx, []⟩
  have typeAt : access.placeType? site.place = some info.ty := by
    exact tyPlace_accessType (penv := env) moduleEq.symm variablesEq.symm source
  have targetType : target.ty = some info.ty := by
    simp only [AccessEnv.owner, typeAt] at targetAt
    cases rootsAt : access.placeRoots site.place with
    | error error => simp [rootsAt, Functor.map, Except.map] at targetAt
    | ok roots =>
      simp [rootsAt, Functor.map, Except.map] at targetAt
      subst target
      rfl
  rcases shape with grow | shrink
  · simp [DemandOwner.invalidates, targetType, grow]
  · simp [DemandOwner.invalidates, targetType, shrink]

theorem site_owner_invalidates {module : Core.Module} {contextIndex : ContextId}
    {context : Context} {implementation : Impl}
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, implementation, context, []⟩ (.block implementation.body) []
      (lowerEnv module implementation.vars implementation.results.toList) (cfg_implState module implementation)
      (lowerContextAt module context implementation)
      ((lowerContextAt module context implementation).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex site.source.site.source.sourcePath
      site.source.site.source.place site.source.site.source.rhs origin)
    {target : DemandOwner}
    (targetAt : demand.planContext.approvals.access.owner site.source.site.source.place = .ok target) :
    target.invalidates = true := by
  apply site.source.site.source.owner_invalidates (targetAt := targetAt)
  · rw [demand.access_context contextAt implementationAt]
    exact (congrArg LEnv.mod site.source.site.source.environment).symm
  · rw [demand.access_context contextAt implementationAt]
    exact (congrArg LEnv.vars site.source.site.source.environment).symm

#print axioms AcceptedReplacementSite.owner_invalidates
#print axioms site_owner_invalidates

end Goose.Lower.Validation
