import Goose.GIR.ReplacementContentFlowProofsSliceTouchClosure

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def ModuleTouchRows (module : Module) (states : Array State) : Prop :=
  ∀ (index : Nat) (func : Func) (state : State), module.funcs[index]? = some func → states[index]? = some state →
    state.touched.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true)

theorem State.CanonicalWithin.round_touchRows {module : Module} {states : Array State}
    {types : Array (Array (Option VTy))} {provenances : Array Prov}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)} {state : State}
    (before : state.CanonicalWithin func vt provenance)
    (facts : FunctionCanonicalFacts module func vt provenance results)
    (moduleFacts : ModuleCanonicalFacts module types provenances results)
    (inputs : ModuleCanonicalWithin module types provenances states) (supported : ModuleSupported module states)
    (touched : state.touched.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true))
    (inputTouched : ModuleTouchRows module states) :
    (round module states func vt state).touched.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true) := by
  have closed : (round module states func vt state).CanonicalWithin func vt provenance ∧
      (round module states func vt state).touched.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true) := by
    simp only [round,← Array.foldl_toList]
    apply List.foldlRecOn (motive := fun current : State => current.CanonicalWithin func vt provenance ∧
      current.touched.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true))
      func.blocks.toList _ ⟨before,touched⟩
    intro current valid block blockMember
    apply List.foldlRecOn (motive := fun current : State => current.CanonicalWithin func vt provenance ∧
      current.touched.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true)) block.insts _ valid
    intro current valid inst member
    exact ⟨valid.1.step_closed facts moduleFacts inputs supported blockMember member,
      valid.1.step_touchRows facts moduleFacts inputs supported valid.2 inputTouched blockMember member⟩
  exact closed.2

theorem moduleStart_touchRows (module : Module) (types : Array (Array (Option VTy))) :
    ModuleTouchRows module (moduleStart module types) := by
  intro index func state funcAt stateAt
  have same : state = start func (types[index]?.getD #[]) := by
    simpa [moduleStart,funcAt] using stateAt.symm
  subst state
  rw [start_components]
  simp [Roots.AtomsWithin]

theorem ModuleReachable.touchRows {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)} {initial final : Array State}
    (reachable : ModuleReachable module types initial final)
    (facts : ModuleCanonicalFacts module types provenances results)
    (before : ModuleCanonicalWithin module types provenances initial) (finite : ModuleFinite module initial)
    (addresses : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → FunctionAddressesBounded module func)
    (touched : ModuleTouchRows module initial) : ModuleTouchRows module final := by
  induction reachable with
  | refl => exact touched
  | @next current reachable ih =>
      obtain ⟨canonical,supported⟩ := reachable.canonicalWithin facts before finite addresses
      intro index func state funcAt stateAt
      obtain ⟨prior,priorAt,priorBound⟩ := canonical.2 index func funcAt
      have same : state = round module current func (types[index]?.getD #[]) prior := by
        simpa [moduleRound,funcAt,priorAt] using stateAt.symm
      subst state
      exact priorBound.round_touchRows (facts.functions index func funcAt) facts canonical supported.1
        (ih index func prior funcAt priorAt) ih

theorem close_touchRows {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)} {final : Array State}
    (facts : ModuleCanonicalFacts module types provenances results)
    (annotations : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → annotationsValid module func = true)
    (entries : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func →
      ∀ entry : Block, func.blocks[0]? = some entry → entry.params.length ≤ func.params.length)
    (addresses : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → FunctionAddressesBounded module func)
    (closed : close module types = some final) : ModuleTouchRows module final :=
  (close_reachable closed).touchRows facts (moduleStart_canonicalWithin facts)
    (moduleStart_finite _ _ annotations entries) addresses (moduleStart_touchRows _ _)

theorem close_touched_known {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)} {final : Array State}
    (facts : ModuleCanonicalFacts module types provenances results)
    (annotations : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → annotationsValid module func = true)
    (entries : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func →
      ∀ entry : Block, func.blocks[0]? = some entry → entry.params.length ≤ func.params.length)
    (addresses : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → FunctionAddressesBounded module func)
    (closed : close module types = some final)
    {index : Nat} {func : Func} {state : State} (funcAt : module.funcs[index]? = some func)
    (stateAt : final[index]? = some state) : ∃ roots, normalize func state.touched = some roots := by
  have bounded := close_touchRows facts annotations entries addresses closed index func state funcAt stateAt
  apply bounded.normalize
  have growth := (close_initial_extends closed).values index
  have initialAt : (moduleStart module types)[index]? = some (start func (types[index]?.getD #[])) := by
    simp [moduleStart,funcAt]
  simp only [initialAt,stateAt,Option.getD_some] at growth
  apply growth.touched.ready
  rw [start_components]
  simp

#print axioms State.CanonicalWithin.round_touchRows
#print axioms ModuleReachable.touchRows
#print axioms close_touched_known

end Goose.GIR.ReplacementContentFlow.Model
