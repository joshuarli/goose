import Goose.Core.DeclarativeRoots
import Goose.Lower.Validation.SourceSymbolAnnotationFacts
import Goose.Lower.Validation.ReplacementContentFlowSourceSeedFloors
import Goose.Lower.Validation.SourceCanonicalRootFloorsSeeds

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

 theorem lowerContext_canonical_refSlice_slot_seed_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {contextIndex : ContextId} {context : Context} {impl : Impl}
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl) {slot : VarId} {localVar : LocalVar}
    (variableAt : impl.vars[slot]? = some localVar) (reference : localVar.ty.isRefSlice = true)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    RootRef.param slot ∈ rootsAt
      ((lowerContextAt module context impl).provenance results types rootCount).slots slot := by
  obtain ⟨parameter, parameterAt, identity, _⟩ :=
    SummaryPreservation.accepted_refSlice_parameter accepted implAt variableAt reference
  obtain ⟨foundImpl, foundAt, checked⟩ := (validate_modOk module accepted).ctx contextIndex context contextAt
  rw [implAt] at foundAt
  cases foundAt
  have refLike : localVar.ty.isRefLike = true := by
    cases shape : localVar.ty <;> simp_all [Ty.isRefSlice, Ty.isRefLike]
  have annotation : ∃ declared, (slot, declared) ∈ context.varRoots := by
    cases found : context.varRoots.find? (·.1 == slot) with
    | none =>
      have empty : context.varRoots.filter (·.1 == slot) = [] :=
        List.filter_eq_nil_iff.mpr (List.find?_eq_none.mp found)
      have count := (Core.Declarative.annotations_sound module impl context checked.annotationShape).2.1
        slot localVar variableAt refLike
      rw [empty] at count
      cases count
    | some row =>
      have key : row.1 = slot := by
        simpa using (List.find?_some (p := fun candidate : Nat × List RootRef => candidate.1 == slot) found)
      exact ⟨row.2, by simpa only [← key] using List.mem_of_find?_eq_some found⟩
  obtain ⟨declared, annotation⟩ := annotation
  apply SourceCanonicalRootFloors.canonical_slot_seed_floor results types _ rootCount slot (.param slot)
  exact ReplacementContentFlowSource.lowerContext_slot_seed_parameter
    variableAt reference parameterAt identity annotation

#print axioms lowerContext_canonical_refSlice_slot_seed_of_accepted

end Goose.Lower.Validation
