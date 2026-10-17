import Goose.Lower.Validation.ReplacementContentFlowSourceReadyHolders
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger
import Goose.GIR.ReplacementContentFlowProofsCanonicalInvariant
import Goose.Core.Sound.Check
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReadBounds

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem CallArgumentPhysical.content_ready {func : Func} {types : Array (Option VTy)} {state : State}
    {provenance ghost : Prov} {env : PEnv} {typingEnv : TEnv} {syntaxArg : Arg} {value : ValueId}
    {mutability nativeMutability : Mutability} {place : Place} {info : PlaceInfo} {startOffset finishOffset : Nat}
    (physical : CallArgumentPhysical env syntaxArg ghost value)
    (canonical : state.CanonicalWithin func types provenance)
    (growth : (start func types).Extends state)
    (sourceArg : syntaxArg = .byRef mutability place)
    (shape : ∃ varId, place = .var varId ∨
      (place = .deref (.read (.var varId)) ∧ env.isRefSliceVar varId = true ∧ (env.cont varId).isSome = true))
    (sourcePlace : Core.tyPlace typingEnv place startOffset = .ok (info, finishOffset))
    (reference : info.ty.isRefLike = true)
    (slots : VisibleSlotsReady typingEnv state)
    (bounded : value < state.values.size)
    (native : types[value]? = some (some (.data (.ref nativeMutability info.ty))))
    (below : rootsAt provenance.vals value ⊆ rootsAt ghost.vals value)
    (available : flowAt state.values value ≠ .pending) :
    content func state (flowAt state.values value) ≠ .pending := by
  have origins := canonical.holderValues value bounded nativeMutability info.ty native reference
  have address := physical mutability place sourceArg shape
  cases address with
  | «local» variableId placeEq exactRoots =>
    subst place
    have checked := sourcePlace
    simp only [Core.tyPlace] at checked
    obtain ⟨localVar, offset, lookup, typedInfo⟩ := (st_bind_ok _ _ _ _).mp checked
    obtain ⟨visible, variableRow, _⟩ := (varOf_ok _ _ _ _).mp lookup
    have infoType : info.ty = localVar.ty := by
      exact congrArg PlaceInfo.ty (congrArg Prod.fst ((st_pure_ok _ _ _).mp typedInfo))
    apply holder_content_ready origins available
    · intro slot member
      have same : slot = variableId := by simpa only [exactRoots, List.mem_singleton, RootRef.local.injEq] using below member
      subst slot
      exact slots variableId visible localVar variableRow (by simpa only [infoType] using reference)
    · intro index _
      exact contents_ready_of_initial_extends growth index
  | contents variableId placeEq refSlice exactRoots =>
    apply holder_parameter_content_ready growth origins available
    intro slot member
    have impossible := below member
    simp [exactRoots] at impossible

theorem ReadAddressPhysical.local_content_ready {func : Func} {types : Array (Option VTy)} {state : State}
    {provenance : Prov} {env : PEnv} {place : Place} {roots : List RootRef} {value : ValueId}
    {typingEnv : TEnv} {variableId : VarId} {info : PlaceInfo} {startOffset finishOffset : Nat}
    {nativeMutability : Mutability}
    (physical : ReadAddressPhysical env place roots)
    (canonical : state.CanonicalWithin func types provenance)
    (growth : (start func types).Extends state)
    (source : Core.tyPlace typingEnv (.var variableId) startOffset = .ok (info, finishOffset))
    (reference : info.ty.isRefLike = true)
    (slots : VisibleSlotsReady typingEnv state)
    (bounded : value < state.values.size)
    (native : types[value]? = some (some (.data (.ref nativeMutability info.ty))))
    (below : rootsAt provenance.vals value ⊆ roots)
    (member : RootRef.local variableId ∈ rootsAt provenance.vals value)
    (available : flowAt state.values value ≠ .pending) :
    content func state (flowAt state.values value) ≠ .pending := by
  have upper := physical.local_upper below member
  have origins := canonical.holderValues value bounded nativeMutability info.ty native reference
  have checked := source
  simp only [Core.tyPlace] at checked
  obtain ⟨localVar, offset, lookup, typedInfo⟩ := (st_bind_ok _ _ _ _).mp checked
  obtain ⟨visible, variableRow, _⟩ := (varOf_ok _ _ _ _).mp lookup
  have infoType : info.ty = localVar.ty :=
    congrArg PlaceInfo.ty (congrArg Prod.fst ((st_pure_ok _ _ _).mp typedInfo))
  apply holder_content_ready origins available
  · intro slot member
    have same : slot = variableId := by simpa using upper member
    subst slot
    exact slots variableId visible localVar variableRow (by simpa only [infoType] using reference)
  · intro index _
    exact contents_ready_of_initial_extends growth index

theorem ReadAddressPhysical.parameter_content_ready {func : Func} {types : Array (Option VTy)} {state : State}
    {provenance : Prov} {env : PEnv} {place : Place} {roots : List RootRef} {value : ValueId}
    {index : Nat} {payload : Ty} {nativeMutability : Mutability}
    (physical : ReadAddressPhysical env place roots)
    (canonical : state.CanonicalWithin func types provenance)
    (growth : (start func types).Extends state)
    (reference : payload.isRefLike = true)
    (bounded : value < state.values.size)
    (native : types[value]? = some (some (.data (.ref nativeMutability payload))))
    (below : rootsAt provenance.vals value ⊆ roots)
    (member : RootRef.param index ∈ rootsAt provenance.vals value)
    (available : flowAt state.values value ≠ .pending) :
    content func state (flowAt state.values value) ≠ .pending := by
  have upper := physical.parameter_upper below member
  have origins := canonical.holderValues value bounded nativeMutability payload native reference
  apply holder_parameter_content_ready growth origins available
  intro slot member
  have impossible := upper member
  simp at impossible

#print axioms ReadAddressPhysical.local_content_ready
#print axioms ReadAddressPhysical.parameter_content_ready

#print axioms CallArgumentPhysical.content_ready

end Goose.Lower.Validation.ReplacementContentFlowSource
