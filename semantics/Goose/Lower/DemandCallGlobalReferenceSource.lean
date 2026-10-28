import Goose.Lower.DemandCallLoopMixedSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem ArgSource.global_reference_type {cfg : Cfg} {env : Env} {state : St} {global : GlobalId}
    {mutability : Mutability} (source : ArgSource cfg env state (.byRef mutability (.global global)))
    (shrink : cfg.mod.profile = .shrink) :
    ∃ (place : PlaceSource cfg env (.global global) state),
      place.rootsEnv.access.placeType? (.global global) = some place.ty ∧ place.ty.refTarget = true := by
  cases source with
  | byRef mutability place target =>
    have targetType : place.ty.refTarget = true := by
      rcases target with target | ⟨_, _, impossible⟩
      · exact target
      · simp [Place.sliceArg, Place.derefVar?] at impossible
    have matchEnv : place.typingEnv.mod = place.rootsEnv.mod ∧ place.typingEnv.vars = place.rootsEnv.impl.vars := by
      have access := place.access
      cases context : place.context with
      | pilot profile active =>
        have impossible := profile.symm.trans shrink
        cases impossible
      | shrink profile context =>
        simp only [EvaluationContext.AccessMatches, context] at access
        exact ⟨access.1.symm.trans access.2.2.1, access.2.1.symm.trans (congrArg Impl.vars access.2.2.2.1)⟩
    exact ⟨place, tyPlace_accessType matchEnv.1 matchEnv.2 place.typed, targetType⟩

#print axioms ArgSource.global_reference_type
end Goose.Lower
