import Goose.GIR.ReplacementContentFlowProofsTouchFootprintSteps

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def ModuleTouchFootprints (module : Module) (types : Array (Array (Option VTy)))
    (policy : Func → Atom → Prop) (states : Array State) : Prop :=
  ∀ (index : Nat) (func : Func) (state : State), module.funcs[index]? = some func → states[index]? = some state →
    state.TouchFootprint func (types[index]?.getD #[]) (policy func)

theorem moduleStart_touchFootprints {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)} (policy : Func → Atom → Prop)
    (facts : ModuleCanonicalFacts module types provenances results) :
    ModuleTouchFootprints module types policy (moduleStart module types) := by
  intro index func state funcAt stateAt
  have same : state = start func (types[index]?.getD #[]) := by
    simpa only [moduleStart,Array.getElem?_mapIdx,funcAt,Option.map_some,Option.some.injEq] using stateAt.symm
  subst state
  exact start_touchFootprint (policy func) (facts.functions index func funcAt)

theorem State.TouchFootprint.round {module : Module} {states : Array State} {func : Func}
    {types : Array (Array (Option VTy))} {localTypes : Array (Option VTy)}
    {provenances : Array Prov} {provenance : Prov} {results : Array (List RootRef)}
    {policy : Atom → Prop} {state : State}
    (before : state.TouchFootprint func localTypes policy)
    (canonical : state.CanonicalWithin func localTypes provenance)
    (facts : FunctionCanonicalFacts module func localTypes provenance results)
    (moduleFacts : ModuleCanonicalFacts module types provenances results)
    (inputs : ModuleCanonicalWithin module types provenances states)
    (supported : ModuleSupported module states)
    (preserved : ∀ (current : State) (block : Block), block ∈ func.blocks.toList → ∀ inst, inst ∈ block.insts →
      current.TouchFootprint func localTypes policy → current.CanonicalWithin func localTypes provenance →
      (Model.step module states func localTypes current inst).TouchFootprint func localTypes policy) :
    (Model.round module states func localTypes state).TouchFootprint func localTypes policy := by
  have result : (Model.round module states func localTypes state).TouchFootprint func localTypes policy ∧
      (Model.round module states func localTypes state).CanonicalWithin func localTypes provenance := by
    simp only [Model.round,← Array.foldl_toList]
    apply List.foldlRecOn (motive := fun current : State => current.TouchFootprint func localTypes policy ∧
      current.CanonicalWithin func localTypes provenance) func.blocks.toList _ ⟨before,canonical⟩
    intro current valid block blockMember
    apply List.foldlRecOn (motive := fun current : State => current.TouchFootprint func localTypes policy ∧
      current.CanonicalWithin func localTypes provenance) block.insts _ valid
    intro current valid inst member
    exact ⟨preserved current block blockMember inst member valid.1 valid.2,
      valid.2.step_closed facts moduleFacts inputs supported blockMember member⟩
  exact result.1

#print axioms moduleStart_touchFootprints
#print axioms State.TouchFootprint.round

end Goose.GIR.ReplacementContentFlow.Model
