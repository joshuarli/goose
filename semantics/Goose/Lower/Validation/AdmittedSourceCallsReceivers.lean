import Goose.Lower.Validation.AdmittedSourceCallsContentRows
import Goose.GIR.RootBoundsRefinement

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.GIR

theorem lowerContextRootCeiling_refines (module : Core.Module) (context : Context) (impl : Impl)
    (declared : List RootRef) :
    GIR.RootsRefine (lowerContextAt module context impl)
      (lowerContextRootCeiling context impl declared) declared := by
  intro root member
  rcases Core.Sound.unionRoots_mem _ _ _ member with literal | alias
  · exact .inl literal
  · obtain ⟨⟨formal, index⟩, formalMember, selected⟩ := List.mem_filterMap.mp alias
    have formalAt : impl.params[index]? = some formal := by
      simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp formalMember
    cases annotation : context.varRoots.find? (·.1 == formal.var) with
    | none => simp [annotation] at selected
    | some entry =>
      simp only [annotation] at selected
      split at selected
      · rename_i subset
        cases Option.some.inj selected
        refine .inr ?_
        intro concrete concreteMember
        have domain := SummaryPreservation.lowerContextAt_parameterRoots_eq (module := module) (ctx := context)
          formalAt (roots := entry.2) (by simp [annotation])
        exact Core.Sound.subsetRoots_mem subset concrete
          (by simpa only [Func.expandParameterRoot, domain] using concreteMember)
      · simp at selected

theorem local_receiver_source_bounds
    {module : Core.Module} {context : Context} {impl : Impl} {provenance : Prov}
    {slot : SlotId} {declared mapped : List RootRef}
    (stored : rootsAt provenance.slots slot = lowerContextRootCeiling context impl declared)
    (lower : mapped ⊆ declared) (upper : declared ⊆ mapped) :
    GIR.RootsRefine (lowerContextAt module context impl)
      ((lowerContextAt module context impl).receiverContentCeiling provenance (.local slot)) mapped ∧
      mapped ⊆ (lowerContextAt module context impl).receiverContentCeiling provenance (.local slot) := by
  simp only [Func.receiverContentCeiling, stored]
  constructor
  · exact (lowerContextRootCeiling_refines module context impl declared).source_mono upper
  · intro root member
    exact Core.Sound.unionRoots_left _ _ root (lower member)

theorem parameter_receiver_source_bounds
    {func : Func} {provenance : Prov} {parameter : Nat} {declared mapped : List RootRef}
    (reference : (func.params[parameter]?).any Ty.isRefSlice = true)
    (contents : func.contentRoots parameter = declared)
    (lower : mapped ⊆ declared) (upper : declared ⊆ mapped) :
    GIR.RootsRefine func (func.receiverContentCeiling provenance (.param parameter)) mapped ∧
      mapped ⊆ func.receiverContentCeiling provenance (.param parameter) := by
  simp only [Func.receiverContentCeiling, reference, ite_true, contents]
  exact ⟨fun _ member => .inl (upper member), lower⟩

end Goose.Lower.Validation.AdmittedSourceCalls
