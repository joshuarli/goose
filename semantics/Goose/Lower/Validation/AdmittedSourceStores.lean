import Goose.GIR.AdmittedRegions
import Goose.Lower.Validation.SummaryPreservationRootRefinement
import Goose.Lower.Validation.SummaryPreservationParameters

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerContextAt_admitted_store_of_source {module : Core.Module}
    {context : Context} {impl : Impl} {env : PEnv} (contextEq : env.ctx = context)
    {index : Nat} {parameter : Param} (parameterAt : impl.params[index]? = some parameter)
    {sourceRoots : List RootRef}
    (source : Core.checkStore env (.deref (.read (.var parameter.var))) sourceRoots = .ok ())
    (reference : env.isRefSliceVar parameter.var = true)
    {provenance : Prov} {types : Array (Option VTy)} {address value : ValueId} {origin : Option OriginId}
    (addressRoots : ∀ root ∈ rootsAt provenance.vals address, root = .param index)
    (valueRoots : SummaryPreservation.RootsRefine (lowerContextAt module context impl)
      (rootsAt provenance.vals value) sourceRoots) :
    (lowerContextAt module context impl).admittedInstruction (lower module) types provenance
      (.eff (.store address value origin)) = true := by
  obtain ⟨ceiling, contentAt, included⟩ := Core.Sound.checkStore_ok env _ sourceRoots source
    parameter.var rfl reference
  have annotation : (context.contentRoots.find? (·.1 == parameter.var)).map (·.2) = some ceiling := by
    simpa only [PEnv.cont, contextEq] using contentAt
  have nativeAnnotation := SummaryPreservation.lowerContextRootInfo_contents_eq parameterAt annotation
  have within : (lowerContextAt module context impl).rootsWithin (rootsAt provenance.vals value) ceiling = true := by
    apply (Func.rootsWithin_eq_true _ _ _).mpr
    exact valueRoots.source_mono included
  simp only [Func.admittedInstruction, Bool.or_eq_true]
  apply Or.inr
  apply List.all_eq_true.mpr
  intro root member
  rw [addressRoots root member]
  have actualAnnotation : ((lowerContextAt module context impl).roots.contents.find? (·.1 == index)) =
      some (index, ceiling) := nativeAnnotation
  simp [actualAnnotation, within]

#print axioms lowerContextAt_admitted_store_of_source

end Goose.Lower.Validation
