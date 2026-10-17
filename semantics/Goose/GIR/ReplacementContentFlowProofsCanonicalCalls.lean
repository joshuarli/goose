import Goose.GIR.ReplacementContentFlowProofsCanonicalTransfer
import Goose.GIR.ReplacementContentFlowProofsCalls

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem mapRawContentRoots_member (provenance : Prov) (args : List ValueId)
    (roots : List RootRef) (root : RootRef) :
    root ∈ mapRawContentRoots provenance args roots ↔
      ∃ original ∈ roots, root ∈ mapRawContentRoots provenance args [original] := by
  simp only [mapRawContentRoots,List.mem_eraseDups,List.flatMap_singleton,List.mem_flatMap]

theorem RootsRefine.mapRaw {caller callee : Func} {provenance : Prov} {args : List ValueId}
    {actual source : List RootRef}
    (contracts : ∀ index, RootsRefine caller (mapRawContentRoots provenance args [.param index])
      (mapRawContentRoots provenance args (callee.parameterRoots index)))
    (bounded : RootsRefine callee actual source) :
    RootsRefine caller (mapRawContentRoots provenance args actual)
      (mapRawContentRoots provenance args source) := by
  let mapping := fun root => mapRawContentRoots provenance args [root]
  have bounds := bounded.map mapping (by
    intro index
    exact (contracts index).source_mono (fun root member =>
      List.mem_flatMap.mpr ((mapRawContentRoots_member _ _ _ _).mp member)))
  apply RootsRefine.source_mono (RootsRefine.actual_mono bounds ?_) ?_
  · intro root member
    exact List.mem_flatMap.mpr ((mapRawContentRoots_member _ _ _ _).mp member)
  · intro root member
    exact (mapRawContentRoots_member _ _ _ _).mpr (List.mem_flatMap.mp member)

theorem SymbolicRootsRefine.substitute {module : Module} {caller callee : Func} {state : State} {args : List ValueId}
    {provenance : Prov} {roots : Roots} {source : List RootRef}
    (closed : ∀ index root, root ∈ caller.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (bounded : SymbolicRootsRefine callee roots source)
    (supported : roots.Supported (atomUniverse module callee))
    (external : ∀ slot, RootRef.local slot ∉ source)
    (contracts : ∀ index, RootsRefine caller (mapRawContentRoots provenance args [.param index])
      (mapRawContentRoots provenance args (callee.parameterRoots index)))
    (arguments : ∀ index, index < callee.params.length → ∃ value, args[index]? = some value ∧
      SymbolicRootsRefine caller (flowAt state.values value)
        (mapRawContentRoots provenance args [.param index]))
    (contentArguments : ∀ index ceiling, index < callee.params.length →
      callee.roots.contents.find? (·.1 == index) = some (index,ceiling) →
      ∃ value, args[index]? = some value ∧
        SymbolicRootsRefine caller (content caller state (flowAt state.values value))
          (mapRawContentRoots provenance args ceiling)) :
    SymbolicRootsRefine caller (substitute caller state args roots)
      (mapRawContentRoots provenance args source) := by
  rcases bounded with rfl | ⟨symbolic,known,within⟩
  · exact .pending _ _
  · obtain ⟨atoms,rfl⟩ := normalize_known_shape known
    have atomKnowledge := (normalize_fold_atoms _ atoms [] symbolic known).2
    apply SymbolicRootsRefine.bind_known
    intro atom member
    obtain ⟨mapped,mappedKnown,mappedWithin⟩ := atomKnowledge atom member
    have atomSupported := supported.2 member
    have atomBound : RootsRefine callee mapped source := within.actual_mono mappedWithin
    have transported := RootsRefine.mapRaw contracts atomBound
    cases atom with
    | «local» slot =>
        have mappedValue : mapped = [.local slot] := Option.some.inj mappedKnown.symm
        subst mapped
        have impossible := atomBound (.local slot) (by simp)
        exact False.elim (impossible.elim (external slot)
          (fun expanded => external slot (expanded _ (by simp [Func.expandParameterRoot]))))
    | global global =>
        have mappedValue : mapped = [.global global] := Option.some.inj mappedKnown.symm
        subst mapped
        apply SymbolicRootsRefine.refine closed ?_ transported
        apply (SymbolicRootsRefine.global_iff caller global _).mpr
        simp [mapRawContentRoots]
    | param index =>
        have mappedValue : mapped = [.param index] := Option.some.inj mappedKnown.symm
        subst mapped
        obtain ⟨value,argument,argumentBound⟩ := arguments index ((atomUniverse_param _ _ _).mp atomSupported)
        simp only [argument,Option.map_some,Option.getD_some]
        exact argumentBound.refine closed transported
    | contents index =>
        cases annotation : callee.roots.contents.find? (·.1 == index) with
        | none => simp [normalizeAtom,annotation] at mappedKnown
        | some row =>
            have selection := Array.find?_some annotation
            have identity : row.1 = index := by simpa only [beq_iff_eq] using selection
            rcases row with ⟨selected,ceiling⟩
            change selected = index at identity
            subst selected
            have mappedValue : mapped = ceiling :=
              Option.some.inj (mappedKnown.symm.trans (symbolicAtom_contents annotation))
            subst mapped
            obtain ⟨value,argument,contentBound⟩ := contentArguments index ceiling ((atomUniverse_contents _ _ _).mp atomSupported) annotation
            simp only [argument,Option.map_some,Option.getD_some]
            exact contentBound.refine closed transported

theorem State.CanonicalMemory.call_content {func : Func} {provenance : Prov} {state : State}
    {address : ValueId} {payload : Ty} {expected : List RootRef}
    (before : state.CanonicalMemory func provenance) (shape : state.Shape func)
    (physical : HolderRoots func payload (rootsAt provenance.vals address) (flowAt state.values address))
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (reference : payload.isRefLike = true)
    (observed : ∀ index, RootRef.param index ∈ rootsAt provenance.vals address →
      (func.params[index]?).any Ty.isRefSlice = true →
      (func.roots.contents.find? (·.1 == index)).isSome = true)
    (receivers : ∀ root ∈ rootsAt provenance.vals address,
      RootsRefine func (func.receiverContentCeiling provenance root) expected) :
    SymbolicRootsRefine func (content func state (flowAt state.values address)) expected := by
  apply physical.content_symbolic_typed parameters reference
  · intro slot storage row _ target
    have bound : slot < state.slots.size := by
      rw [shape.slots]
      exact (Array.getElem?_eq_some_iff.mp row).choose
    exact (before.slots slot bound).refine closed (receivers (.local slot) target)
  · intro index mutability row target
    have slice := paramOk_refLike_payload parameters row reference
    have observed := observed index target (by simp [row,slice])
    have bound : index < state.contents.size := by
      rw [shape.contents]
      exact (List.getElem?_eq_some_iff.mp row).choose
    apply (before.contents index bound observed).refine closed
    simpa [Func.receiverContentCeiling,row,slice] using receivers (.param index) target

theorem call_result_symbolic {module : Module} {states : Array State} {caller callee : Func}
    {state effects : State} {args : List ValueId} {fn : FnId} {provenance : Prov}
    {returned : List RootRef}
    (calleeAt : module.funcs[fn]? = some callee) (effectsAt : states[fn]? = some effects)
    (closed : ∀ index root, root ∈ caller.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (bounded : SymbolicRootsRefine callee effects.returned returned)
    (supported : effects.returned.Supported (atomUniverse module callee))
    (external : ∀ slot, RootRef.local slot ∉ returned)
    (contracts : ∀ index, RootsRefine caller (mapRawContentRoots provenance args [.param index])
      (mapRawContentRoots provenance args (callee.parameterRoots index)))
    (arguments : ∀ index, index < callee.params.length → ∃ value, args[index]? = some value ∧
      SymbolicRootsRefine caller (flowAt state.values value)
        (mapRawContentRoots provenance args [.param index]))
    (contents : ∀ index ceiling, index < callee.params.length →
      callee.roots.contents.find? (·.1 == index) = some (index,ceiling) →
      ∃ value, args[index]? = some value ∧
        SymbolicRootsRefine caller (content caller state (flowAt state.values value))
          (mapRawContentRoots provenance args ceiling)) :
    SymbolicRootsRefine caller (callState module states caller state fn args).1
      (mapRawContentRoots provenance args returned) := by
  rw [callState_result _ _ _ _ _ _ _ _ calleeAt effectsAt]
  exact bounded.substitute closed supported external contracts arguments contents

#print axioms RootsRefine.mapRaw
#print axioms SymbolicRootsRefine.substitute

end Goose.GIR.ReplacementContentFlow.Model
