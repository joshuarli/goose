import Goose.GIR.ReplacementContentFlowProofsTouchFootprintDefinitions
import Goose.GIR.ReplacementContentFlowProofsAssignedOriginsCalls

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem publicTouches_atomsWithin {roots : Roots} {predicate : Atom → Prop}
    (bounded : roots.AtomsWithin predicate) :
    (publicTouches roots).AtomsWithin (fun atom => predicate atom ∧ ∀ slot, atom ≠ .local slot) := by
  cases roots with
  | pending => trivial
  | unknown => exact False.elim bounded
  | known atoms =>
      apply Roots.AtomsWithin.bind_known
      intro atom member
      cases atom with
      | «local» slot => simp [Roots.AtomsWithin]
      | global index | param index | contents index =>
          all_goals intro actual singleton
          all_goals simp only [List.mem_singleton] at singleton
          all_goals subst actual
          all_goals exact ⟨bounded _ member,by intros; simp⟩

theorem substitute_atomsWithin {func : Func} {state : State} {args : List ValueId}
    {roots : Roots} {before after : Atom → Prop}
    (bounded : roots.AtomsWithin before)
    (mapped : ∀ atom, before atom →
      (match atom with
        | .global global => Roots.known [.global global]
        | .param index => (args[index]?).map (flowAt state.values ·) |>.getD .unknown
        | .contents index => (args[index]?).map (fun value => content func state (flowAt state.values value)) |>.getD .unknown
        | .local _ => .unknown).AtomsWithin after) :
    (substitute func state args roots).AtomsWithin after := by
  cases roots with
  | pending => trivial
  | unknown => exact False.elim bounded
  | known atoms =>
      exact Roots.AtomsWithin.bind_known atoms _ (fun atom member => mapped atom (bounded atom member))

theorem State.TouchFootprint.callState {module : Module} {states : Array State} {func : Func}
    {types calleeTypes : Array (Option VTy)} {provenance calleeProvenance : Prov}
    {policy calleePolicy : Atom → Prop} {state effects : State} {fn : FnId} {args : List ValueId}
    (before : state.TouchFootprint func types policy)
    (canonical : state.CanonicalWithin func types provenance)
    (site : CallSiteFacts module func types provenance fn args)
    (effectsAt : states[fn]? = some effects)
    (effectsFootprint : effects.TouchFootprint site.callee calleeTypes calleePolicy)
    (effectsCanonical : effects.CanonicalWithin site.callee calleeTypes calleeProvenance)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (calleeRoots : FunctionRootFacts site.callee)
    (supported : effects.Supported (atomUniverse module site.callee))
    (touchRows : effects.touched.AtomsWithin (fun atom => (normalizeAtom site.callee atom).isSome = true))
    (mapped : ∀ roots, roots.AtomsWithin (TouchFootprintAtom site.callee calleePolicy) →
      roots.Supported (atomUniverse module site.callee) →
      roots.AtomsWithin (fun atom => (normalizeAtom site.callee atom).isSome = true) →
      roots.AtomsWithin (fun atom => ∀ slot, atom ≠ .local slot) →
      (substitute func state args roots).AtomsWithin (TouchFootprintAtom func policy)) :
    (Model.callState module states func state fn args).2.TouchFootprint func types policy := by
  have publicBound := publicTouches_atomsWithin effectsFootprint.touched
  have callBound := mapped (publicTouches effects.touched)
    (publicBound.mono (fun _ member => member.1)) (publicTouches_supported supported.touched)
    ((publicTouches_normalizableAtoms touchRows).mono (fun _ member => member.1)) (publicBound.mono (fun _ member => member.2))
  rw [callState_fold module states func state fn args site.callee effects site.calleeAt effectsAt]
  apply List.foldlRecOn (motive := fun current : State => current.TouchFootprint func types policy)
    site.callee.params.zipIdx _ (before.touch (before.touched.join callBound))
  intro current valid parameter member
  have formal := List.mem_zipIdx_iff_getElem?.mp member
  unfold callWriteStep
  by_cases reference : parameter.1.isRefSlice = true
  · simp only [reference,ite_true]
    cases writeRow : effects.writes[parameter.2]?.getD (.assigned .unknown) with
    | unchanged => exact valid
    | assigned roots =>
        obtain ⟨outer,inner,element,same,flat⟩ := isRefSlice_shape reference
        have typedFormal : site.callee.params[parameter.2]? = some (.ref outer (.slice inner element)) := by
          simpa only [same] using formal
        obtain ⟨argument,actualMutability,argumentAt,typed,bounded⟩ := site.references _ _ _ typedFormal
        have physical := canonical.holderValues argument
          (by rw [canonical.shape.values]; exact bounded) actualMutability (.slice inner element) typed rfl
        have indexBound : parameter.2 < effects.writes.size := by
          rw [effectsCanonical.shape.writes]
          exact (List.getElem?_eq_some_iff.mp formal).1
        have actualAt : effects.writes[parameter.2]? = some (.assigned roots) := by
          have present := Array.getElem?_eq_getElem indexBound
          rw [present] at writeRow
          rw [present]
          simpa only [Option.getD_some] using congrArg some writeRow
        have assignedBound := effectsFootprint.writes _ _ actualAt
        have symbolic := effectsCanonical.memory.writes parameter.2 indexBound
        simp only [writeRow,Write.SymbolicRefine] at symbolic
        have external := symbolic.externalAtoms (calleeRoots.contentExternal parameter.2)
        simp only [argumentAt,Option.map_some,Option.getD_some]
        exact valid.write parameters physical rfl (fun _ => mapped roots assignedBound (by
          exact supported.writes (.assigned roots) (by simpa using Array.mem_of_getElem? actualAt)) symbolic.normalizableAtoms external)
  · simpa only [reference,Bool.false_eq_true,ite_false] using valid

theorem State.TouchFootprint.call {module : Module} {states : Array State} {func : Func}
    {types calleeTypes : Array (Option VTy)} {provenance calleeProvenance : Prov} {results : Array (List RootRef)}
    {policy calleePolicy : Atom → Prop} {state effects : State} {fn value : ValueId}
    {args : List ValueId} {origin : Option OriginId} {block : Block}
    (before : state.TouchFootprint func types policy)
    (canonical : state.CanonicalWithin func types provenance)
    (facts : FunctionCanonicalFacts module func types provenance results)
    (site : CallSiteFacts module func types provenance fn args)
    (effectsAt : states[fn]? = some effects)
    (effectsFootprint : effects.TouchFootprint site.callee calleeTypes calleePolicy)
    (effectsCanonical : effects.CanonicalWithin site.callee calleeTypes calleeProvenance)
    (calleeRoots : FunctionRootFacts site.callee)
    (supported : effects.Supported (atomUniverse module site.callee))
    (touchRows : effects.touched.AtomsWithin (fun atom => (normalizeAtom site.callee atom).isSome = true))
    (mapped : ∀ roots, roots.AtomsWithin (TouchFootprintAtom site.callee calleePolicy) →
      roots.Supported (atomUniverse module site.callee) →
      roots.AtomsWithin (fun atom => (normalizeAtom site.callee atom).isSome = true) →
      roots.AtomsWithin (fun atom => ∀ slot, atom ≠ .local slot) →
      (substitute func state args roots).AtomsWithin (TouchFootprintAtom func policy))
    (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    (step module states func types state (.def value (.call fn args origin))).TouchFootprint func types policy := by
  have after := before.callState canonical site effectsAt effectsFootprint effectsCanonical
    facts.roots.parameters calleeRoots supported touchRows mapped
  have assigned : ({ (Model.callState module states func state fn args).2 with
      values := addFlow (Model.callState module states func state fn args).2.values value
        (if valRefLike types value then (Model.callState module states func state fn args).1 else .known []) } : State).TouchFootprint func types policy := by
    apply after.addValue
    intro actual actualType interior
    by_cases reference : valRefLike types value = true
    · simp only [reference,ite_true,callState_result _ _ _ _ _ _ _ _ site.calleeAt effectsAt]
      rcases facts.callResults block blockMember value fn args origin called site.callee site.calleeAt with
        ⟨empty,unit⟩ | ⟨type,result,resultType⟩
      · simp [valRefLike,unit,VTy.refLike,Ty.isRefLike] at reference
      · have same : actual = .data type := Option.some.inj (Option.some.inj (actualType.symm.trans resultType))
        subst actual
        have like : type.isRefLike = true := by simpa [valRefLike,resultType,VTy.refLike] using reference
        exact mapped effects.returned (effectsFootprint.returned type result interior) supported.returned
          (effectsCanonical.returned type result like).normalizableAtoms
          ((effectsCanonical.returned type result like).externalAtoms calleeRoots.resultExternal)
    · simp [reference,Roots.AtomsWithin]
  simpa only [step,Id.run_pure,interiorLoadedResults,loadedResults,List.filter_nil,
    Model.touchValues,List.foldl_nil] using assigned

#print axioms State.TouchFootprint.callState
#print axioms State.TouchFootprint.call

end Goose.GIR.ReplacementContentFlow.Model
