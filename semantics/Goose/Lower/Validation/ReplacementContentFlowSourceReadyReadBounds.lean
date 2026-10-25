import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger
import Goose.GIR.ReplacementContentFlowProofsCanonicalClosure

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem ReadAddressPhysical.local_upper {env : PEnv} {place : Place} {physicalRoots actual : List RootRef}
    {variableId : VarId} (physical : ReadAddressPhysical env place physicalRoots)
    (below : actual ⊆ physicalRoots) (member : RootRef.local variableId ∈ actual) :
    actual ⊆ [.local variableId] := by
  have literal := below member
  cases physical with
  | «local» index source exactRoots =>
    rw [exactRoots] at literal
    have same : variableId = index := by simpa using literal
    simpa only [same, exactRoots] using below
  | contents index source reference exactRoots =>
    simp [exactRoots] at literal

theorem ReadAddressPhysical.parameter_upper {env : PEnv} {place : Place} {physicalRoots actual : List RootRef}
    {index : Nat} (physical : ReadAddressPhysical env place physicalRoots)
    (below : actual ⊆ physicalRoots) (member : RootRef.param index ∈ actual) :
    actual ⊆ [.param index] := by
  have literal := below member
  cases physical with
  | «local» variableId source exactRoots =>
    simp [exactRoots] at literal
  | contents variableId source reference exactRoots =>
    rw [exactRoots] at literal
    have same : index = variableId := by simpa using literal
    simpa only [same, exactRoots] using below

theorem ReadOccurrence.slot_address_upper {env : PEnv} {root : DemandNode} {func : Func}
    {actual ghost : Prov} {results : Array (List RootRef)} {types : Array (Option VTy)}
    {value address : ValueId} {variableId : VarId}
    (occurrence : ReadOccurrence env root func ghost value address)
    (below : rootsAt actual.vals address ⊆ rootsAt ghost.vals address)
    (bounded : address < actual.vals.size)
    (quiet : func.provStep results types (actual, false) (.def address (.slotAddr variableId)) = (actual, false)) :
    rootsAt actual.vals address ⊆ [.local variableId] := by
  obtain ⟨localEnv, path, place, before, placeRoots, placeAfter, valueRoots, after, access,
    source, placeReplay, readReplay, addressBound, valueBound, addressRefined, valueRefined, physical⟩ := occurrence
  apply physical.local_upper below
  exact provStep_def_roots bounded quiet (by simp [rootsOfDef])

theorem load_local_parameter_seed {func : Func} {actual : Prov} {results : Array (List RootRef)}
    {types : Array (Option VTy)} {value address : ValueId} {slot : SlotId} {index : Nat}
    (bounded : value < actual.vals.size)
    (quiet : func.provStep results types (actual, false) (.def value (.load address)) = (actual, false))
    (reference : valRefLike types value = true)
    (addressMember : RootRef.local slot ∈ rootsAt actual.vals address)
    (seed : RootRef.param index ∈ rootsAt actual.slots slot) :
    RootRef.param index ∈ rootsAt actual.vals value := by
  apply provStep_def_roots bounded quiet
  simp only [rootsOfDef, reference, ite_true]
  apply (unionRoots_mem_iff _ _ _).mpr
  exact Or.inl (List.mem_flatMap.mpr ⟨.local slot, addressMember, seed⟩)

#print axioms ReadAddressPhysical.local_upper
#print axioms ReadAddressPhysical.parameter_upper
#print axioms ReadOccurrence.slot_address_upper
#print axioms load_local_parameter_seed

end Goose.Lower.Validation.ReplacementContentFlowSource
