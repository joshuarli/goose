import Goose.GIR.ReplacementContentFlowProofsSliceTransfer

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem SymbolicRootsRefine.externalAtoms {func : Func} {roots : Roots} {upper : List RootRef}
    (bounded : SymbolicRootsRefine func roots upper) (external : ∀ slot, RootRef.local slot ∉ upper) :
    roots.AtomsWithin (fun atom => ∀ slot, atom ≠ .local slot) := by
  cases roots with
  | pending => trivial
  | unknown => exact False.elim (bounded.not_unknown rfl)
  | known atoms =>
      intro atom member slot same
      subst atom
      exact bounded.local_not_mem external slot member

theorem State.SliceOrigins.call {module : Module} {states finalStates : Array State} {func : Func}
    {types calleeTypes : Array (Option VTy)} {provenance calleeProvenance : Prov}
    {results : Array (List RootRef)} {state final effects finalEffects : State}
    {fn value : ValueId} {args : List ValueId} {origin : Option OriginId}
    {observed calleeObserved : List Atom}
    (before : state.SliceOrigins func types observed)
    (facts : FunctionCanonicalFacts module func types provenance results)
    (site : CallSiteFacts module func types provenance fn args)
    (effectsAt : states[fn]? = some effects) (finalEffectsAt : finalStates[fn]? = some finalEffects)
    (effectsBounded : effects.CanonicalWithin site.callee calleeTypes calleeProvenance)
    (effectsOrigins : effects.SliceOrigins site.callee calleeTypes calleeObserved)
    (effectsSupport : effects.Supported (atomUniverse module site.callee))
    (calleeRoots : FunctionRootFacts site.callee)
    (finalCanonical : final.CanonicalWithin func types provenance)
    (finalRows : finalEffects.touched.AtomsWithin (fun atom => (normalizeAtom site.callee atom).isSome = true))
    (finalSupport : finalEffects.Supported (atomUniverse module site.callee))
    (calleeTouches : finalEffects.touched = .known calleeObserved)
    (growth : state.Extends final)
    (fixed : step module finalStates func types final (.def value (.call fn args origin)) = final)
    (touches : final.touched = .known observed)
    (available : CallObservationReady site.callee func final args)
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    (step module states func types state (.def value (.call fn args origin))).SliceOrigins func types observed := by
  have observedBound : final.touched.AtomsWithin (SliceOrigin func observed) := by
    rw [touches]
    intro atom member
    exact Or.inl member
  constructor
  · rw [step_def_values]
    apply before.values.addFlow
    intro mutability element canonical
    have like : valRefLike types value = true := by simp [valRefLike,canonical,VTy.refLike,Ty.isRefLike]
    simp only [like,ite_true]
    rw [callState_result _ _ _ _ _ _ _ _ site.calleeAt effectsAt,substitute_touchValues]
    rcases facts.callResults block blockMember value fn args origin called site.callee site.calleeAt with
      ⟨empty,unit⟩ | ⟨result,resultType,resultCanonical⟩
    · rw [unit] at canonical
      cases canonical
    · have same : result = .slice mutability element :=
        VTy.data.inj (Option.some.inj (Option.some.inj (resultCanonical.symm.trans canonical)))
      subst result
      have original := effectsOrigins.returned mutability element resultType
      have external := (effectsBounded.returned _ resultType rfl).externalAtoms calleeRoots.resultExternal
      have observed := fixed_call_touches_atomsWithin finalCanonical site finalEffectsAt fixed observedBound
      rw [calleeTouches] at observed finalRows
      have publicSupport := finalSupport.touched
      rw [calleeTouches] at publicSupport
      apply substitute_slice_origins growth original external effectsSupport.returned finalRows
        publicSupport available observed
      intro index mutability element formal argument actual
      obtain ⟨actualMutability,canonical,bounded⟩ := call_slice_argument_type facts site blockMember called formal actual
      exact before.values argument (by rw [growth.values.size,finalCanonical.shape.values]; exact bounded)
        actualMutability element canonical
  · intro mutability element result
    simpa only [step_returned] using before.returned mutability element result

#print axioms State.SliceOrigins.call

end Goose.GIR.ReplacementContentFlow.Model
