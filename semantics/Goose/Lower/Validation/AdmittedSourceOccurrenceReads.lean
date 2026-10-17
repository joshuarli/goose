import Goose.Lower.Validation.AdmittedSourceInstructionsObserved
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem ReplacementContentFlowSource.ReadOccurrence.parameter_observed
    {module : Core.Module} {context : Context} {impl : Impl} {implementation : ImplId}
    {env : PEnv} {root : DemandNode} {provenance upper : Prov}
    {value address : ValueId} {parameter : Nat}
    (accepted : Core.validate module = .ok ())
    (implementationFound : module.impls[implementation]? = some impl)
    (access : env.access = ⟨module, impl, context⟩)
    (occurrence : ReadOccurrence env root (lowerContextAt module context impl) upper value address)
    (below : rootsAt provenance.vals address ⊆ rootsAt upper.vals address)
    (member : RootRef.param parameter ∈ rootsAt provenance.vals address) :
    ((lowerContextAt module context impl).roots.contents.find? (·.1 == parameter)).isSome = true := by
  obtain ⟨localEnv, path, place, before, placeRoots, placeAfter, valueRoots, after,
    localAccess, node, placeReplay, valueReplay, addressBound, valueBound,
    addressRefined, valueRefined, physical⟩ := occurrence
  cases physical with
  | «local» variableId source exactRoots =>
    have impossible := below member
    rw [exactRoots] at impossible
    simp at impossible
  | contents variableId source reference exactRoots =>
    subst place
    exact AdmittedSourceInstructions.lowerContextAt_read_parameter_observed_below
      accepted implementationFound (congrArg AccessEnv.impl (localAccess.trans access))
      (congrArg AccessEnv.ctx (localAccess.trans access)) reference valueReplay exactRoots below member

theorem ReplacementContentFlowSource.InstructionOccurrences.load_observed
    {module : Core.Module} {context : Context} {impl : Impl} {implementation : ImplId}
    {env : PEnv} {root : DemandNode} {provenance upper : Prov}
    {types : Array (Option VTy)} {inst : Inst} {value address : ValueId} {parameter : Nat}
    (accepted : Core.validate module = .ok ())
    (implementationFound : module.impls[implementation]? = some impl)
    (access : env.access = ⟨module, impl, context⟩)
    (occurrence : InstructionOccurrences env root (lowerContextAt module context impl) types upper inst)
    (load : inst = .def value (.load address)) (reference : valRefLike types value = true)
    (below : rootsAt provenance.vals address ⊆ rootsAt upper.vals address)
    (member : RootRef.param parameter ∈ rootsAt provenance.vals address) :
    ((lowerContextAt module context impl).roots.contents.find? (·.1 == parameter)).isSome = true :=
  (occurrence.2.1 value address load reference).parameter_observed
    accepted implementationFound access below member

end Goose.Lower.Validation
